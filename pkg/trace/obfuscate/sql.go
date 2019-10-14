// Unless explicitly stated otherwise all files in this repository are licensed
// under the Apache License Version 2.0.
// This product includes software developed at Datadog (https://www.datadoghq.com/).
// Copyright 2016-2019 Datadog, Inc.

package obfuscate

import (
	"bytes"
	"errors"
	"fmt"
	"strings"

	"github.com/DataDog/datadog-agent/pkg/trace/config"
	"github.com/DataDog/datadog-agent/pkg/trace/metrics"
	"github.com/DataDog/datadog-agent/pkg/trace/pb"
	"github.com/DataDog/datadog-agent/pkg/util/log"
)

const sqlQueryTag = "sql.query"

// tokenFilter is a generic interface that a sqlObfuscator expects. It defines
// the Filter() function used to filter or replace given tokens.
// A filter can be stateful and keep an internal state to apply the filter later;
// this can be useful to prevent backtracking in some cases.

// tokenFilter implementations are meant to process each token in a query one by one and
// potentially return transformed tokens.
type tokenFilter interface {
	// Filter takes the current token kind, the last token kind and the token itself,
	// returning the new token kind and the value that should be stored in the final query,
	// along with an error.
	Filter(token, lastToken TokenKind, buffer []byte) (TokenKind, []byte, error)

	// Reset resets the filter.
	Reset()
}

// discardFilter is a token filter which discards certain elements from a query, such as
// comments and AS aliases by returning a nil buffer.
type discardFilter struct{}

// Filter the given token so that a `nil` slice is returned if the token is in the token filtered list.
func (f *discardFilter) Filter(token, lastToken TokenKind, buffer []byte) (TokenKind, []byte, error) {
	// filters based on previous token
	switch lastToken {
	case FilteredBracketedIdentifier:
		if token != ']' {
			// we haven't found the closing bracket yet, keep going
			if token != ID {
				// the token between the brackets *must* be an identifier,
				// otherwise the query is invalid.
				return LexError, nil, fmt.Errorf("expected identifier in bracketed filter, got %d", token)
			}
			return FilteredBracketedIdentifier, nil, nil
		}
		fallthrough
	case As:
		if token == '[' {
			// the identifier followed by AS is an MSSQL bracketed identifier
			// and will continue to be discarded until we find the corresponding
			// closing bracket counter-part. See GitHub issue DataDog/datadog-trace-agent#475.
			return FilteredBracketedIdentifier, nil, nil
		}
		return Filtered, nil, nil
	}

	// filters based on the current token; if the next token should be ignored,
	// return the same token value (not FilteredGroupable) and nil
	switch token {
	case As:
		return As, nil, nil
	case Comment, ';':
		return FilteredGroupable, nil, nil
	default:
		return token, buffer, nil
	}
}

// Reset implements tokenFilter.
func (f *discardFilter) Reset() {}

// replaceFilter is a token filter which obfuscates strings and numbers in queries by replacing them
// with the "?" character.
type replaceFilter struct{}

// Filter the given token so that it will be replaced if in the token replacement list
func (f *replaceFilter) Filter(token, lastToken TokenKind, buffer []byte) (tokenType TokenKind, tokenBytes []byte, err error) {
	switch lastToken {
	case Savepoint:
		return FilteredGroupable, []byte("?"), nil
	case '=':
		switch token {
		case DoubleQuotedString:
			// double-quoted strings after assignments are eligible for obfuscation
			return FilteredGroupable, []byte("?"), nil
		}
	}
	switch token {
	case String, Number, Null, Variable, PreparedStatement, BooleanLiteral, EscapeSequence:
		return FilteredGroupable, []byte("?"), nil
	default:
		return token, buffer, nil
	}
}

// Reset implements tokenFilter.
func (f *replaceFilter) Reset() {}

// groupingFilter is a token filter which groups together items replaced by the replaceFilter. It is meant
// to run immediately after it.
type groupingFilter struct {
	groupFilter int
	groupMulti  int
}

// Filter the given token so that it will be discarded if a grouping pattern
// has been recognized. A grouping is composed by items like:
//   * '( ?, ?, ? )'
//   * '( ?, ? ), ( ?, ? )'
func (f *groupingFilter) Filter(token, lastToken TokenKind, buffer []byte) (tokenType TokenKind, tokenBytes []byte, err error) {
	// increasing the number of groups means that we're filtering an entire group
	// because it can be represented with a single '( ? )'
	if (lastToken == '(' && token == FilteredGroupable) || (token == '(' && f.groupMulti > 0) {
		f.groupMulti++
	}

	switch {
	case token == FilteredGroupable:
		// the previous filter has dropped this token so we should start
		// counting the group filter so that we accept only one '?' for
		// the same group
		f.groupFilter++

		if f.groupFilter > 1 {
			return FilteredGroupable, nil, nil
		}
	case f.groupFilter > 0 && (token == ',' || token == '?'):
		// if we are in a group drop all commas
		return FilteredGroupable, nil, nil
	case f.groupMulti > 1:
		// drop all tokens since we're in a counting group
		// and they're duplicated
		return FilteredGroupable, nil, nil
	case token != ',' && token != '(' && token != ')' && token != FilteredGroupable:
		// when we're out of a group reset the filter state
		f.Reset()
	}

	return token, buffer, nil
}

// Reset resets the groupingFilter so that it may be used again.
func (f *groupingFilter) Reset() {
	f.groupFilter = 0
	f.groupMulti = 0
}

// tableFinderFilter is a filter which attempts to identify the table name as it goes through each
// token in a query.
type tableFinderFilter struct {
	// names keeps track of unique table names encountered by the filter, as the map keys.
	names map[string]struct{}
}

func newTableFinder() *tableFinderFilter { return &tableFinderFilter{names: make(map[string]struct{})} }

// Filter implements tokenFilter.
func (f *tableFinderFilter) Filter(token, lastToken TokenKind, buffer []byte) (TokenKind, []byte, error) {
	switch lastToken {
	case From, Update, Into, Join:
		// SELECT ... FROM [tableName]
		// DELETE FROM [tableName]
		// UPDATE [tableName]
		// INSERT INTO [tableName]
		// ... JOIN [tableName]
		f.names[string(buffer)] = struct{}{}
	}
	return token, buffer, nil
}

// Names returns all the table names found by the filter.
func (f *tableFinderFilter) Names() []string {
	var names []string
	for name := range f.names {
		names = append(names, name)
	}
	return names
}

// Reset implements tokenFilter.
func (f *tableFinderFilter) Reset() {
	for k := range f.names {
		delete(f.names, k)
	}
}

// obfuscateSQLString attempts to obfuscate the given SQL string, returning the final value, the table
// names found in the query and any error.
func obfuscateSQLString(in string) (sql string, tableNames []string, err error) {
	tokenizer := NewSQLTokenizer(in)
	tableFinder := newTableFinder()
	filters := []tokenFilter{
		&discardFilter{},
		&replaceFilter{},
		&groupingFilter{},
		tableFinder,
	}
	var (
		out       bytes.Buffer
		lastToken TokenKind
	)
	// call Scan() function until tokens are available or if a LEX_ERROR is raised. After
	// retrieving a token, send it to the tokenFilter chains so that the token is discarded
	// or replaced.
	token, buff := tokenizer.Scan()
	for ; token != EOFChar; token, buff = tokenizer.Scan() {
		if token == LexError {
			return "", nil, tokenizer.Err()
		}
		for _, f := range filters {
			if token, buff, err = f.Filter(token, lastToken, buff); err != nil {
				return "", nil, err
			}
		}
		if buff != nil {
			if out.Len() != 0 {
				switch token {
				case ',':
				case '=':
					if lastToken == ':' {
						// do not add a space before an equals if a colon was
						// present before it.
						break
					}
					fallthrough
				default:
					out.WriteRune(' ')
				}
			}
			out.Write(buff)
		}
		lastToken = token
	}
	if out.Len() == 0 {
		return "", nil, errors.New("result is empty")
	}
	return out.String(), tableFinder.Names(), nil
}

func (o *Obfuscator) obfuscateSQL(span *pb.Span) {
	tags := []string{"type:sql"}
	defer func() {
		metrics.Count("datadog.trace_agent.obfuscations", 1, tags, 1)
	}()
	if span.Resource == "" {
		tags = append(tags, "outcome:empty-resource")
		return
	}
	result, tableNames, err := obfuscateSQLString(span.Resource)
	if err != nil {
		// we have an error, discard the SQL to avoid polluting user resources.
		log.Debugf("Error parsing SQL query: %v. Resource: %q", err, span.Resource)
		if span.Meta == nil {
			span.Meta = make(map[string]string, 1)
		}
		if _, ok := span.Meta[sqlQueryTag]; !ok {
			span.Meta[sqlQueryTag] = span.Resource
		}
		span.Resource = "Non-parsable SQL query"
		tags = append(tags, "outcome:error")
		return
	}

	tags = append(tags, "outcome:success")
	span.Resource = result

	if config.HasFeature("table_names") && len(tableNames) > 0 {
		if span.Meta == nil {
			span.Meta = make(map[string]string)
		}
		// only add the first for now, until we support list tags
		span.Meta["sql.table"] = tableNames[0]
		if len(tableNames) > 1 {
			span.Meta["sql.tables"] = strings.Join(tableNames, ",")
		}
	}
	if span.Meta != nil && span.Meta[sqlQueryTag] != "" {
		// "sql.query" tag already set by user, do not change it.
		return
	}
	if span.Meta == nil {
		span.Meta = make(map[string]string)
	}
	span.Meta[sqlQueryTag] = result
}

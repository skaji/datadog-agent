// +build linux

package netlink

import (
	"crypto/rand"
	"encoding/binary"
	"fmt"
	"net"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/DataDog/datadog-agent/pkg/process/util"

	ct "github.com/florianl/go-conntrack"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestIsNat(t *testing.T) {
	c := map[ct.ConnAttrType][]byte{
		ct.AttrOrigIPv4Src: {1, 1, 1, 1},
		ct.AttrOrigIPv4Dst: {2, 2, 2, 2},

		ct.AttrReplIPv4Src: {2, 2, 2, 2},
		ct.AttrReplIPv4Dst: {1, 1, 1, 1},
	}
	assert.False(t, isNAT(c))
}

func TestRegisterNonNat(t *testing.T) {
	rt := newConntracker()
	c := makeUntranslatedConn("10.0.0.0:8080", "50.30.40.10:12345")

	rt.register(c)
	translation := rt.GetTranslationForConn(util.AddressFromString("10.0.0.0"), 8080)
	assert.Nil(t, translation)
}

func TestRegisterNat(t *testing.T) {
	rt := newConntracker()
	c := makeTranslatedConn("10.0.0.0:12345", "50.30.40.10:80", "20.0.0.0:80")

	rt.register(c)
	translation := rt.GetTranslationForConn(util.AddressFromString("10.0.0.0"), 12345)
	assert.NotNil(t, translation)
	assert.Equal(t, &IPTranslation{
		ReplSrcIP:   util.AddressFromString("20.0.0.0"),
		ReplDstIP:   util.AddressFromString("10.0.0.0"),
		ReplSrcPort: 80,
		ReplDstPort: 12345,
	}, translation)

	// even after unregistering, we should be able to access the conn
	rt.unregister(c)
	translation2 := rt.GetTranslationForConn(util.AddressFromString("10.0.0.0"), 12345)
	assert.NotNil(t, translation2)

	// double unregisters should never happen, though it will be treated as a no-op
	rt.unregister(c)

	rt.ClearShortLived()
	translation3 := rt.GetTranslationForConn(util.AddressFromString("10.0.0.0"), 12345)
	assert.Nil(t, translation3)

	// triple unregisters should never happen, though it will be treated as a no-op
	rt.unregister(c)

	assert.Equal(t, translation, translation2)

}

func TestGetUpdatesGen(t *testing.T) {
	rt := newConntracker()
	c := makeTranslatedConn("10.0.0.0:12345", "50.30.40.10:80", "20.0.0.0:80")

	rt.register(c)
	var last uint8
	for _, v := range rt.state {
		v.expGeneration -= 5
		last = v.expGeneration
		break // there is only one item in the map
	}

	iptr := rt.GetTranslationForConn(util.AddressFromString("10.0.0.0"), 12345)
	require.NotNil(t, iptr)

	for _, v := range rt.state {
		assert.NotEqual(t, last, v.expGeneration)
		break // there is only one item in the map
	}
}

// Run this test with -memprofile to get an insight of how much memory is
// allocated/used by Conntracker to store maxStateSize entries.
// Example: go test -run TestConntrackerMemoryAllocation -memprofile mem.prof .
func TestConntrackerMemoryAllocation(t *testing.T) {
	const maxStateSize = 100000
	rt := newConntracker()
	rt.maxStateSize = maxStateSize
	addressGen := randomAddressGen()

	for i := 0; i < rt.maxStateSize; i++ {
		c := makeTranslatedConn(
			fmt.Sprintf("%s:12345", addressGen()),
			fmt.Sprintf("%s:80", addressGen()),
			fmt.Sprintf("%s:80", addressGen()),
		)

		rt.register(c)
	}
}

func newConntracker() *realConntracker {
	return &realConntracker{
		state:               make(map[connKey]*connValue),
		shortLivedBuffer:    make(map[connKey]*IPTranslation),
		maxShortLivedBuffer: 10000,
		compactTicker:       time.NewTicker(time.Hour),
		maxStateSize:        10000,
	}
}

func makeUntranslatedConn(from, to string) ct.Conn {
	return makeTranslatedConn(from, to, to)
}

// makes a translation where from -> to is shows as actualTo -> from
func makeTranslatedConn(from, to, actualTo string) ct.Conn {
	ip, port := parts(from)
	dip, dport := parts(to)
	tip, tport := parts(actualTo)

	return map[ct.ConnAttrType][]byte{
		ct.AttrOrigIPv4Src: ip,
		ct.AttrOrigPortSrc: port,
		ct.AttrOrigIPv4Dst: dip,
		ct.AttrOrigPortDst: dport,

		ct.AttrReplIPv4Src: tip,
		ct.AttrReplPortSrc: tport,
		ct.AttrReplIPv4Dst: ip,
		ct.AttrReplPortDst: port,
	}
}

// splits an IP:port string into network order byte representations of IP and port.
// IPv4 only.
func parts(p string) ([]byte, []byte) {
	segments := strings.Split(p, ":")
	prt, _ := strconv.ParseUint(segments[1], 10, 16)
	b := make([]byte, 2)
	binary.BigEndian.PutUint16(b, uint16(prt))

	ip := net.ParseIP(segments[0]).To4()

	return ip, b
}

func randomAddressGen() func() util.Address {
	b := make([]byte, 4)
	return func() util.Address {
		for {
			if _, err := rand.Read(b); err != nil {
				continue
			}

			return util.V4AddressFromBytes(b)
		}
	}
}

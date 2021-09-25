package main

import "C"
import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm/runtime"
)

//export CreateTrace
func CreateTrace(code string) *C.char {
	address := common.BytesToAddress([]byte{0xff})

	contracts := []Contract{{Address: address, Bytecode: []byte(code)}}

	logs, err := TraceTx(address, nil, &runtime.Config{GasLimit: 100}, contracts)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to trace tx, err: %v\n", err)
	}

	bytes, err := json.MarshalIndent(logs, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to marshal logs, err: %v\n", err)
	}

	return C.CString(string(bytes))
}

func main() {}

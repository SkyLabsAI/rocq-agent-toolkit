  $ cat > calls.txt <<EOF
  > run [0,"Inductive n := Zero : n | Succ : n -> n."]
  > run [0,"Require Import Stdlib.ZArith.BinInt."]
  > run [0,"Require Import Stdlib.ZArith.BinIntt"]
  > run [0,"Require Import Stdlib.ZArith.BinInk."]
  >   
  > run [0,"Lemma test : 0 = 0."]
  > run [0,"Proof."]
  > run [0,"reflexivity."]
  > run [0,"Qed."]
  > run [37,"About test."]
  > back_to [3]
  > 
  > run [37,"About test."]
  > quit
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests
  {"jsonrpc":"2.0","method":"run","id":1,"params":[0,"Inductive n := Zero : n | Succ : n -> n."]}
  {"jsonrpc":"2.0","method":"run","id":2,"params":[0,"Require Import Stdlib.ZArith.BinInt."]}
  {"jsonrpc":"2.0","method":"run","id":3,"params":[0,"Require Import Stdlib.ZArith.BinIntt"]}
  {"jsonrpc":"2.0","method":"run","id":4,"params":[0,"Require Import Stdlib.ZArith.BinInk."]}
  {"jsonrpc":"2.0","method":"run","id":5,"params":[0,"Lemma test : 0 = 0."]}
  {"jsonrpc":"2.0","method":"run","id":6,"params":[0,"Proof."]}
  {"jsonrpc":"2.0","method":"run","id":7,"params":[0,"reflexivity."]}
  {"jsonrpc":"2.0","method":"run","id":8,"params":[0,"Qed."]}
  {"jsonrpc":"2.0","method":"run","id":9,"params":[37,"About test."]}
  {"jsonrpc":"2.0","method":"back_to","id":10,"params":[3]}
  {"jsonrpc":"2.0","method":"run","id":11,"params":[37,"About test."]}
  {"jsonrpc":"2.0","method":"quit","id":12}

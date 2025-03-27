  $ cat > requests.txt <<EOF
  > {"jsonrpc":"2.0","method":"run","id":1,"params":[0,"Inductive n := Zero : n | Succ : n -> n."]}
  > {"jsonrpc":"2.0","method":"run","id":2,"params":[0,"Require Import Stdlib.ZArith.BinInt."]}
  > {"jsonrpc":"2.0","method":"run","id":3,"params":[0,"Require Import Stdlib.ZArith.BinIntt"]}
  > {"jsonrpc":"2.0","method":"run","id":4,"params":[0,"Require Import Stdlib.ZArith.BinInk."]}
  > {"jsonrpc":"2.0","method":"run","id":5,"params":[0,"Lemma test : 0 = 0."]}
  > {"jsonrpc":"2.0","method":"run","id":6,"params":[0,"Proof."]}
  > {"jsonrpc":"2.0","method":"run","id":7,"params":[0,"reflexivity."]}
  > {"jsonrpc":"2.0","method":"run","id":8,"params":[0,"Qed."]}
  > {"jsonrpc":"2.0","method":"run","id":9,"params":[37,"About test."]}
  > {"jsonrpc":"2.0","method":"back_to","id":10,"params":[3]}
  > {"jsonrpc":"2.0","method":"run","id":11,"params":[37,"About test."]}
  > {"jsonrpc":"2.0","method":"quit","id":12}
  > EOF

  $ cat requests.txt | jsonrpc-tp.tp_wrap
  Content-Length: 96
  
  {"jsonrpc":"2.0","method":"run","id":1,"params":[0,"Inductive n := Zero : n | Succ : n -> n."]}
  Content-Length: 92
  
  {"jsonrpc":"2.0","method":"run","id":2,"params":[0,"Require Import Stdlib.ZArith.BinInt."]}
  Content-Length: 92
  
  {"jsonrpc":"2.0","method":"run","id":3,"params":[0,"Require Import Stdlib.ZArith.BinIntt"]}
  Content-Length: 92
  
  {"jsonrpc":"2.0","method":"run","id":4,"params":[0,"Require Import Stdlib.ZArith.BinInk."]}
  Content-Length: 75
  
  {"jsonrpc":"2.0","method":"run","id":5,"params":[0,"Lemma test : 0 = 0."]}
  Content-Length: 62
  
  {"jsonrpc":"2.0","method":"run","id":6,"params":[0,"Proof."]}
  Content-Length: 68
  
  {"jsonrpc":"2.0","method":"run","id":7,"params":[0,"reflexivity."]}
  Content-Length: 60
  
  {"jsonrpc":"2.0","method":"run","id":8,"params":[0,"Qed."]}
  Content-Length: 68
  
  {"jsonrpc":"2.0","method":"run","id":9,"params":[37,"About test."]}
  Content-Length: 58
  
  {"jsonrpc":"2.0","method":"back_to","id":10,"params":[3]}
  Content-Length: 69
  
  {"jsonrpc":"2.0","method":"run","id":11,"params":[37,"About test."]}
  Content-Length: 42
  
  {"jsonrpc":"2.0","method":"quit","id":12}

  $ cat requests.txt | jsonrpc-tp.tp_wrap | jsonrpc-tp.tp_unwrap
  {"id":1,"params":[0,"Inductive n := Zero : n | Succ : n -> n."],"method":"run","jsonrpc":"2.0"}
  {"id":2,"params":[0,"Require Import Stdlib.ZArith.BinInt."],"method":"run","jsonrpc":"2.0"}
  {"id":3,"params":[0,"Require Import Stdlib.ZArith.BinIntt"],"method":"run","jsonrpc":"2.0"}
  {"id":4,"params":[0,"Require Import Stdlib.ZArith.BinInk."],"method":"run","jsonrpc":"2.0"}
  {"id":5,"params":[0,"Lemma test : 0 = 0."],"method":"run","jsonrpc":"2.0"}
  {"id":6,"params":[0,"Proof."],"method":"run","jsonrpc":"2.0"}
  {"id":7,"params":[0,"reflexivity."],"method":"run","jsonrpc":"2.0"}
  {"id":8,"params":[0,"Qed."],"method":"run","jsonrpc":"2.0"}
  {"id":9,"params":[37,"About test."],"method":"run","jsonrpc":"2.0"}
  {"id":10,"params":[3],"method":"back_to","jsonrpc":"2.0"}
  {"id":11,"params":[37,"About test."],"method":"run","jsonrpc":"2.0"}
  {"id":12,"method":"quit","jsonrpc":"2.0"}

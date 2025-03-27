  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > calls.txt <<EOF
  > run [0,"Inductive n := Zero : n | Succ : n -> n."]
  > run [0,"Require Import Stdlib.ZArith.BinInt."]
  > run [0,"Require Import Stdlib.ZArith.BinIntt"]
  > run [0,"Require Import Stdlib.ZArith.BinInk."]
  > run [0,"Lemma test : 0 = 0."]
  > run [0,"Proof."]
  > run [0,"reflexivity."]
  > run [0,"Qed."]
  > run [37,"About test."]
  > back_to [3]
  > run [37,"About test."]
  > quit
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-jsonrpc-repl | jsonrpc-tp.tp_unwrap
  {"id":1,"jsonrpc":"2.0","result":{"success":true,"state":2,"feedback":[{"kind":"info","text":"n is defined"},{"kind":"info","text":"n_rect is defined"},{"kind":"info","text":"n_ind is defined"},{"kind":"info","text":"n_rec is defined"},{"kind":"info","text":"n_sind is defined"}]}}
  {"id":2,"jsonrpc":"2.0","result":{"success":true,"state":3}}
  {"id":3,"jsonrpc":"2.0","result":{"success":false,"state":3,"error":"Syntax error: '.' expected after [gallina_ext] (in [vernac_aux]).","loc":{"fname":["ToplevelInput"],"line_nb":1,"bol_pos":0,"line_nb_last":1,"bol_pos_last":0,"bp":36,"ep":37}}}
  {"id":4,"jsonrpc":"2.0","result":{"success":false,"state":3,"error":"Cannot find a physical path bound to logical path Stdlib.ZArith.BinInk.","loc":{"fname":["ToplevelInput"],"line_nb":1,"bol_pos":0,"line_nb_last":1,"bol_pos_last":0,"bp":15,"ep":35},"feedback":[{"kind":"error","loc":{"fname":["ToplevelInput"],"line_nb":1,"bol_pos":0,"line_nb_last":1,"bol_pos_last":0,"bp":15,"ep":35},"text":"Cannot find a physical path bound to logical path Stdlib.ZArith.BinInk."}]}}
  {"id":5,"jsonrpc":"2.0","result":{"success":true,"state":5,"data":"1 goal\n  \n  ============================\n  0 = 0"}}
  {"id":6,"jsonrpc":"2.0","result":{"success":true,"state":6,"data":"1 goal\n  \n  ============================\n  0 = 0"}}
  {"id":7,"jsonrpc":"2.0","result":{"success":true,"state":7,"data":"No more goals."}}
  {"id":8,"jsonrpc":"2.0","result":{"success":true,"state":8}}
  {"id":9,"jsonrpc":"2.0","result":{"success":true,"state":9,"feedback":[{"kind":"notice","text":"test : 0 = 0\n\ntest is not universe polymorphic\ntest is opaque\nExpands to: Constant Top.test\nDeclared in toplevel input, characters 6-10"}]}}
  {"id":10,"jsonrpc":"2.0","result":{"success":true,"state":3}}
  {"id":11,"jsonrpc":"2.0","result":{"success":true,"state":10,"feedback":[{"kind":"notice","text":"test not a defined object."}]}}
  {"id":12,"jsonrpc":"2.0","result":null}

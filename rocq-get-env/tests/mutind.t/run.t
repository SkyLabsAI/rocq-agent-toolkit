  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ coqc -Q . test mutind.v
  $ coqc -Q . test test.v
  {
    "constants": [
      {
        "kername": "test.mutind.tree_sind",
        "about": "tree_sind :\nforall (A B : Type) (P : tree A B -> SProp),\n(forall (a : A) (f : forest A B), P (node a f)) -> forall t : tree A B, P t\n\ntree_sind is not universe polymorphic\nArguments tree_sind (A B)%_type_scope (P f)%_function_scope t\ntree_sind is transparent\nExpands to: Constant test.mutind.tree_sind\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.tree_rect",
        "about": "tree_rect :\nforall (A B : Type) (P : tree A B -> Type),\n(forall (a : A) (f : forest A B), P (node a f)) -> forall t : tree A B, P t\n\ntree_rect is not universe polymorphic\nArguments tree_rect (A B)%_type_scope (P f)%_function_scope t\ntree_rect is transparent\nExpands to: Constant test.mutind.tree_rect\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.forest_sind",
        "about": "forest_sind :\nforall (A B : Type) (P : forest A B -> SProp),\n(forall b : B, P (leaf b)) ->\n(forall (t : tree A B) (f : forest A B), P f -> P (cons t f)) ->\nforall f : forest A B, P f\n\nforest_sind is not universe polymorphic\nArguments forest_sind (A B)%_type_scope (P f f0)%_function_scope f\nforest_sind is transparent\nExpands to: Constant test.mutind.forest_sind\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.forest_rect",
        "about": "forest_rect :\nforall (A B : Type) (P : forest A B -> Type),\n(forall b : B, P (leaf b)) ->\n(forall (t : tree A B) (f : forest A B), P f -> P (cons t f)) ->\nforall f : forest A B, P f\n\nforest_rect is not universe polymorphic\nArguments forest_rect (A B)%_type_scope (P f f0)%_function_scope f\nforest_rect is transparent\nExpands to: Constant test.mutind.forest_rect\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.forest_rec",
        "about": "forest_rec :\nforall (A B : Type) (P : forest A B -> Set),\n(forall b : B, P (leaf b)) ->\n(forall (t : tree A B) (f : forest A B), P f -> P (cons t f)) ->\nforall f : forest A B, P f\n\nforest_rec is not universe polymorphic\nArguments forest_rec (A B)%_type_scope (P f f0)%_function_scope f\nforest_rec is transparent\nExpands to: Constant test.mutind.forest_rec\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.forest_ind",
        "about": "forest_ind :\nforall (A B : Type) (P : forest A B -> Prop),\n(forall b : B, P (leaf b)) ->\n(forall (t : tree A B) (f : forest A B), P f -> P (cons t f)) ->\nforall f : forest A B, P f\n\nforest_ind is not universe polymorphic\nArguments forest_ind (A B)%_type_scope (P f f0)%_function_scope f\nforest_ind is transparent\nExpands to: Constant test.mutind.forest_ind\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.tree_rec",
        "about": "tree_rec :\nforall (A B : Type) (P : tree A B -> Set),\n(forall (a : A) (f : forest A B), P (node a f)) -> forall t : tree A B, P t\n\ntree_rec is not universe polymorphic\nArguments tree_rec (A B)%_type_scope (P f)%_function_scope t\ntree_rec is transparent\nExpands to: Constant test.mutind.tree_rec\nDeclared in library test.mutind, line 1, characters 0-156"
      },
      {
        "kername": "test.mutind.tree_ind",
        "about": "tree_ind :\nforall (A B : Type) (P : tree A B -> Prop),\n(forall (a : A) (f : forest A B), P (node a f)) -> forall t : tree A B, P t\n\ntree_ind is not universe polymorphic\nArguments tree_ind (A B)%_type_scope (P f)%_function_scope t\ntree_ind is transparent\nExpands to: Constant test.mutind.tree_ind\nDeclared in library test.mutind, line 1, characters 0-156"
      }
    ],
    "inductives": [
      {
        "kername": "test.mutind.tree",
        "print": "Inductive tree (A B : Type) : Type :=\n    node : A -> forest A B -> tree A B\n  with forest (A B : Type) : Type :=\n    leaf : B -> forest A B | cons : tree A B -> forest A B -> forest A B.\n  \n  Arguments tree (A B)%_type_scope\n  Arguments node {A B}%_type_scope _ _\n  Arguments forest (A B)%_type_scope\n  Arguments leaf {A B}%_type_scope _\n  Arguments cons {A B}%_type_scope _ _",
        "about": [
          "tree : Type -> Type -> Type\n\ntree is not universe polymorphic\nArguments tree (A B)%_type_scope\nExpands to: Inductive test.mutind.tree\nDeclared in library test.mutind, line 1, characters 10-14",
          "forest : Type -> Type -> Type\n\nforest is not universe polymorphic\nArguments forest (A B)%_type_scope\nExpands to: Inductive test.mutind.forest\nDeclared in library test.mutind, line 3, characters 5-11"
        ]
      }
    ]
  }

From idt Require Import all.
From MetaCoq.Template Require Import utils All.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

Inductive llist (A : Set) : Set :=
| nill  : llist A
| conss : A -> llist A -> llist A.

Arguments nil {A}.
Arguments conss {A} _ _.

Inductive tree (A B : Set) : Set :=
| mempty : tree A B
| mnode : A -> B -> tree A B -> tree A B -> tree A B.


(* ------- EDIT here ------ *)

(* Type being Functorialized *)
Notation T := tree.
(* Functor Name *)
Notation Fname := "treeF".

(* ------------------------ *)


Definition newT : Type.
  let rec go x :=
    match x with
        | forall (A :?Z), ?M =>  refine (forall (A : Z), _); go M
        | ?U => exact (forall (X : Set), U)
    end in
  let Ty := type of T in
  go Ty.
Defined.

Definition newlist : tsf_ctors_ty (newT).
Proof.
  run_template_program (get_ctors T)
                       (fun xs =>
                          let xs := eval simpl in xs in
                          let rec go xs :=
                            lazymatch xs with
                            | (?name, (existT_typed_term ?cty ?ctor)) :: ?xs =>
                                let n := eval compute in (append name "F") in
                                refine ((n, _) :: _); [
                                  intros Hc R; unfold newT in R; tsf_interact ctor R
                                | go xs ]
                            | _ => exact []
                            end
                          in go xs).

  all:
    let rec rector ty := match ty with
                             | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                 try specialize (ctor A);
                                                 pose proof R A as R;
                                                 rector U
                             | _ => idtac
                         end in
    let Ty := type of R in
    rector Ty;
    let rec ctorTy ty := match ty with
                             | forall (_ : _), ?U => ctorTy U
                             | ?U => U
                         end in
    let Ty := type of ctor in
    let Cty := ctorTy Ty in
    let rec go' ty := match ty with
                          | Cty -> ?U => refine (X ->  _); go' U
                          | forall A : ?S, ?U => refine (forall (A : S), _); go' U
                          | Cty => exact R
                      end in
    go' Ty.
Defined.

Arguments newlist /.

Fixpoint extract_params (t : term) (n : nat) : list (aname * term) :=
  match n with
      | O => []
      | S n' => match t with
                   | tProd s ty t' => (s, ty) :: extract_params t' n'
                   | _ => []
               end
  end.

Fixpoint extract_ty_ret (t : term) : term :=
  match t with
      | tProd _ _ t' => extract_ty_ret t'
      | t => t
  end.

Definition mk_indparam (s : aname) (t : term) : context_decl :=
  {| decl_name := s;
    decl_body := None;
    decl_type := t |}.

Definition get_level (t : term) : list LevelSet.elt :=
  match t with
      | tSort (Universe.lType {|Universe.t_set := {| UnivExprSet.this := xs |}
              |}) => map fst xs
      | _ => []
  end.

Fixpoint count_tProds' (n : nat)  (t : term) : nat :=
  match t with
      | tProd _ _ t' => count_tProds' (S n) t'
      | _ => n
  end.

Definition count_tProds := count_tProds' 0.


#[universes(polymorphic)]
Definition ind_gen' (name : ident) (ctors : list (ident * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
  ty <- tmQuote (unfolded newT) ;;
  match nth_error mind.(ind_bodies) i with
  | Some ind =>
      let npars := mind.(ind_npars) + 1 in
      let ctors := map (fun '(n, t) =>
                          let t' := try_remove_n_lambdas 1 t in
                          (n, t', count_tProds t' - npars)) ctors in
      let params := extract_params ty npars in
      let ty_ret := extract_ty_ret ty in
      let indparam := map (fun '(s, t) => mk_indparam s t) params in
      let param_terms := map snd params in
      let lvls := flat_map get_level (ty_ret :: param_terms) in
      let univ := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) in
      let ind' :=
        {| ind_finite := mind.(ind_finite);
           ind_npars := mind.(ind_npars) + 1;
           ind_universes := univ;
           ind_variance := mind.(ind_variance);
           ind_params := indparam;
           ind_bodies := [ {| ind_name := name;
                              ind_type  := ty;
                              ind_kelim := ind.(ind_kelim);
                              ind_ctors := ctors;
                              ind_projs := ind.(ind_projs);
                              ind_relevance := ind.(ind_relevance) |} ]
        |}
      in
      tmMkInductive' ind'
  | _ => tmFail "No body found"
  end.


MetaCoq Run (
          '(mind, i) <- tsf_get_mind ltac:(quote_term T (fun t => exact t));;
          let ctorsT := ltac:(tsf_ctors_to_tm newlist) in
          ind_gen' Fname ctorsT mind i
        ).

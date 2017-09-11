open Bindlib

let debug = ref false

let from_opt_rev : 'a option list -> 'a list = fun l ->
  let fn acc e =
    match e with
    | None   -> acc
    | Some e -> e::acc
  in
  List.fold_left fn [] l

(* AST *)
type te_ex =
  | Te_Var of te_ex var
  | Te_Sym of string
  | Te_Abs of (te_ex, te_ex) binder
  | Te_App of te_ex * te_ex
  | Te_Uni of te_ex option ref
  | Te_Wit of (te_ex, te_ex) binder * ty_ex * ty_ex
  | Te_UWt of te_ex * (te_ex, ty_ex) binder

and ty_ex =
  | Ty_Var of ty_ex var
  | Ty_Sym of string * ty_ex list * te_ex list
  | Ty_Fun of ty_ex * ty_ex
  | Ty_FA2 of (ty_ex, ty_ex) binder
  | Ty_FA1 of (te_ex, ty_ex) binder
  | Ty_Uni of ty_ex option ref
  | Ty_UWt of te_ex * (ty_ex, ty_ex) binder

type te_box = te_ex bindbox
type te_var = te_ex var

type ty_box = ty_ex bindbox
type ty_var = ty_ex var

type rule =
  { def   : (te_ex, te_ex * te_ex) mbinder
  ; symb  : string
  ; arity : int }

let rec unfold_te : te_ex -> te_ex = fun t ->
  match t with
  | Te_Uni(r) -> (match !r with None -> t | Some t -> unfold_te t)
  | _         -> t

let rec unfold_ty : ty_ex -> ty_ex = fun a ->
  match a with
  | Ty_Uni(r) -> (match !r with None -> a | Some a -> unfold_ty a)
  | _         -> a

(* Bindlib's "mkfree" *)
let te_mkfree : te_var -> te_ex =
  fun x -> Te_Var(x)

let ty_mkfree : ty_var -> ty_ex =
  fun x -> Ty_Var(x)

(* Smart constructors *)
let te_sym : string -> te_box =
  fun s -> box (Te_Sym(s))

let te_abs : string -> (te_var -> te_box) -> te_box =
  fun x f -> box_apply (fun b -> Te_Abs(b)) (vbind te_mkfree x f)

let te_app : te_box -> te_box -> te_box =
  box_apply2 (fun t u -> Te_App(t,u))

let ty_sym : string -> ty_box list -> te_box list -> ty_box =
  fun s tys tes ->
    box_apply2 (fun tys tes -> Ty_Sym(s,tys,tes))
      (box_list tys) (box_list tes)

let ty_fun : ty_box -> ty_box -> ty_box =
  box_apply2 (fun a b -> Ty_Fun(a,b))

let ty_fa2 : string -> (ty_var -> ty_box) -> ty_box =
  fun x f -> box_apply (fun b -> Ty_FA2(b)) (vbind ty_mkfree x f)
 
let ty_fa1 : string -> (te_var -> ty_box) -> ty_box =
  fun x f -> box_apply (fun b -> Ty_FA1(b)) (vbind te_mkfree x f)

(* Printing *)
let rec print_te : out_channel -> te_ex -> unit = fun oc t ->
  let rec is_abs t =
    match t with
    | Te_Abs(_) -> true
    | Te_Uni(r) -> (match !r with None -> false | Some t -> is_abs t)
    | _         -> false
  in
  let rec is_app t =
    match t with
    | Te_App(_,_) -> true
    | Te_Abs(_)   -> true
    | Te_Uni(r)   -> (match !r with None -> false | Some t -> is_app t)
    | _           -> false
  in
  match unfold_te t with
  | Te_Var(x)     -> output_string oc (name_of x)
  | Te_Sym(s)     -> output_string oc s
  | Te_Abs(b)     ->
      let (x,t) = unbind te_mkfree b in
      Printf.fprintf oc "λ%s.%a" (name_of x) print_te t
  | Te_App(t,u)   ->
      let (l1,r1) = if is_abs t then ("(",")") else ("","") in
      let (l2,r2) = if is_app u then ("(",")") else ("","") in
      Printf.fprintf oc "%s%a%s %s%a%s" l1 print_te t r1 l2 print_te u r2
  | Te_Uni(r)     -> output_string oc "?"
  | Te_Wit(f,_,_) -> output_string oc ("ε" ^ binder_name f)
  | Te_UWt(_,f)   -> output_string oc ("ε" ^ binder_name f)

let rec print_ty : out_channel -> ty_ex -> unit = fun oc a ->
  let rec is_atom a =
    match a with
    | Ty_Var(_)     -> true
    | Ty_Sym(_,_,_) -> true
    | Ty_Uni(r)     -> (match !r with None -> false | Some a -> is_atom a)
    | _             -> false
  in
  match unfold_ty a with
  | Ty_Var(x)         -> output_string oc (name_of x)
  | Ty_Sym(s,tys,tes) ->
      begin
        output_string oc s;
        match (tys, tes) with
        | ([]     , []     ) -> ()
        | ([]     , te::tes) ->
            Printf.fprintf oc "(%a" print_te te;
            List.iter (Printf.fprintf oc ", %a" print_te) tes;
            Printf.fprintf oc ")"
        | (ty::tys, tes    ) ->
            Printf.fprintf oc "(%a" print_ty ty;
            List.iter (Printf.fprintf oc ", %a" print_ty) tys;
            List.iter (Printf.fprintf oc ", %a" print_te) tes;
            Printf.fprintf oc ")"
      end
  | Ty_Fun(a,b)       ->
      let (l,r) = if is_atom a then ("","") else ("(",")") in
      Printf.fprintf oc "%s%a%s ⇒ %a" l print_ty a r print_ty b
  | Ty_FA2(b)         ->
      let (x,a) = unbind ty_mkfree b in
      Printf.fprintf oc "∀%s.%a" (name_of x) print_ty a
  | Ty_FA1(b)         ->
      let (x,a) = unbind te_mkfree b in
      Printf.fprintf oc "∀%s.%a" (name_of x) print_ty a
  | Ty_Uni(r)         -> output_string oc "?"
  | Ty_UWt(_,f)       -> output_string oc ("ε" ^ binder_name f)

(* Pattern data *)
let pattern_data : te_ex -> (string * int) option = fun t ->
  let rec get_args acc t =
    match t with
    | Te_Sym(s)   -> Some(s, acc)
    | Te_App(t,u) -> get_args (u::acc) t
    | _           -> None
  in
  match get_args [] t with
  | None        -> None
  | Some(s, ts) -> Some(s, List.length ts)

(* Context *)
module SMap = Map.Make(String)
type sign =
  { te_symbols : ty_ex SMap.t
  ; ty_symbols : (int * int) SMap.t
  ; rules      : rule list }

let empty_sign =
  { te_symbols = SMap.empty
  ; ty_symbols = SMap.empty
  ; rules = [] }

type ctxt = (te_var * ty_ex) list

let find : te_var -> ctxt -> ty_ex = fun x ctx ->
  let rec find ctx =
    match ctx with
    | []         -> raise Not_found
    | (y,a)::ctx -> if eq_vars x y then a else find ctx
  in find ctx

let print_ctxt : out_channel -> ctxt -> unit = fun oc ctx ->
  let rec print_vars oc ls =
    match ls with
    | []          ->
        output_string oc "∅"
    | [(x,a)]     ->
        let x = name_of x in
        if x = "_" then output_string oc "∅"
        else Printf.fprintf oc "%s : %a" x print_ty a
    | (x,a)::ctx  ->
        let x = name_of x in
        if x = "_" then print_vars oc ctx
        else Printf.fprintf oc "%a, %s : %a" print_vars ctx x print_ty a
  in print_vars oc ctx

let find_rules : string -> int -> sign -> (int * rule) list = fun s i si ->
  let rec suitable acc rs =
    match rs with
    | []    -> acc
    | r::rs -> if s = r.symb && r.arity <= i then
                 suitable ((i - r.arity, r)::acc) rs
               else suitable acc rs
  in suitable [] si.rules

let remove_args : te_ex -> int -> te_ex * te_ex list = fun t n ->
  let rec rem acc n t =
    assert (n >= 0);
    let t = unfold_te t in
    match (t, n) with
    | (_          , 0) -> (t, acc)
    | (Te_App(t,u), n) -> rem (u::acc) (n-1) t
    | (_          , _) -> assert false
  in
  rem [] n t

let add_args : te_ex -> te_ex list -> te_ex =
  List.fold_left (fun t u -> Te_App(t,u))

(* Equality *)
let dummy_te = Te_Sym("<dummy>")
let dummy_ty = Ty_Sym("<dummy>",[],[])

let rec te_uvar_iter : (te_ex option ref -> unit)
    -> (ty_ex option ref -> unit) -> te_ex -> unit = fun f_te f_ty t ->
  match unfold_te t with
  | Te_Var(_)     -> ()
  | Te_Sym(_)     -> ()
  | Te_Abs(f)     -> te_uvar_iter f_te f_ty (subst f dummy_te)
  | Te_App(t,u)   -> te_uvar_iter f_te f_ty t; te_uvar_iter f_te f_ty u
  | Te_Uni(r)     -> f_te r
  | Te_Wit(f,a,b) -> te_uvar_iter f_te f_ty (subst f dummy_te);
                     ty_uvar_iter f_te f_ty a; ty_uvar_iter f_te f_ty b;
  | Te_UWt(t,f)   -> te_uvar_iter f_te f_ty t;
                     ty_uvar_iter f_te f_ty (subst f dummy_te)

and ty_uvar_iter : (te_ex option ref -> unit)
    -> (ty_ex option ref -> unit) -> ty_ex -> unit = fun f_te f_ty a ->
  match unfold_ty a with
  | Ty_Var(_)       -> ()
  | Ty_Sym(_,l1,l2) -> List.iter (ty_uvar_iter f_te f_ty) l1;
                       List.iter (te_uvar_iter f_te f_ty) l2;
  | Ty_Fun(a,b)     -> ty_uvar_iter f_te f_ty a; ty_uvar_iter f_te f_ty b
  | Ty_FA2(f)       -> ty_uvar_iter f_te f_ty (subst f dummy_ty)
  | Ty_FA1(f)       -> ty_uvar_iter f_te f_ty (subst f dummy_te)
  | Ty_Uni(r)       -> f_ty r
  | Ty_UWt(t,f)     -> te_uvar_iter f_te f_ty t;
                       ty_uvar_iter f_te f_ty (subst f dummy_ty)

exception Found

let ty_uvar_occurs : ty_ex option ref -> ty_ex -> bool = fun u a ->
  try ty_uvar_iter ignore (fun v -> if v == u then raise Found) a; false
  with Found -> true

let te_uvar_occurs : te_ex option ref -> te_ex -> bool = fun u t ->
  try te_uvar_iter (fun v -> if v == u then raise Found) ignore t; false
  with Found -> true

let rec eq_te_ex : ?no_eval:bool -> sign -> te_ex -> te_ex -> bool =
  fun ?(no_eval=false) si t u ->
  let eq_binders b1 b2 =
    let x = free_of (new_var te_mkfree "<dummy>") in
    eq_te_ex ~no_eval si (subst b1 x) (subst b2 x)
  in
  let t = unfold_te t in
  let u = unfold_te u in
  let t = if no_eval then t else eval si t in
  let u = if no_eval then u else eval si u in
  if !debug then Printf.eprintf "DEBUG [%a =?= %a]\n%!" print_te t print_te u;
  match (unfold_te t, unfold_te u) with
  | (t1           , t2           ) when t1 == t2 -> true
  | (Te_Var(x1)   , Te_Var(x2)   ) -> eq_vars x1 x2
  | (Te_Sym(s1)   , Te_Sym(s2)   ) -> s1 = s2
  | (Te_Abs(b1)   , Te_Abs(b2)   ) -> eq_binders b1 b2
  | (Te_App(t1,u1), Te_App(t2,u2)) -> eq_te_ex ~no_eval si t1 t2
                                      && eq_te_ex ~no_eval si u1 u2
  | (Te_Uni(r1)   , Te_Uni(r2)   ) when r1 == r2 -> true
  | (Te_Uni(r)    , t            ) -> if te_uvar_occurs r t then false
                                      else (r := Some(t); true)
  | (t            , Te_Uni(r)    ) -> if te_uvar_occurs r t then false
                                      else (r := Some(t); true)
  | (_            , _            ) -> false

and eq_ty_ex : sign -> ty_ex -> ty_ex -> bool = fun si a b ->
  let a = unfold_ty a in
  let b = unfold_ty b in
  if !debug then Printf.eprintf "DEBUG [%a =?= %a]\n%!" print_ty a print_ty b;
  match (a, b) with
  | (Ty_Var(x1)          , Ty_Var(x2)          ) -> eq_vars x1 x2
  | (Ty_Sym(s1,tys1,tes1), Ty_Sym(s2,tys2,tes2)) ->
      assert (List.length tys1 = List.length tys2);
      assert (List.length tes1 = List.length tes2);
      s1 = s2 && List.for_all2 (eq_ty_ex si) tys1 tys2
      && List.for_all2 (eq_te_ex si) tes1 tes2
  | (Ty_Fun(a1,b1)       , Ty_Fun(a2,b2)       ) ->
      eq_ty_ex si a1 a2 && eq_ty_ex si b1 b2
  | (Ty_FA2(b1)          , Ty_FA2(b2)          ) ->
      let x = free_of (new_var ty_mkfree "<dummy>") in
      eq_ty_ex si (subst b1 x) (subst b2 x)
  | (Ty_FA1(b1)          , Ty_FA1(b2)          ) ->
      let x = free_of (new_var te_mkfree "<dummy>") in
      eq_ty_ex si (subst b1 x) (subst b2 x)
  | (Ty_Uni(r1)          , Ty_Uni(r2)          ) when r1 == r2 -> true
  | (Ty_Uni(r)           , a                   ) ->
      if ty_uvar_occurs r a then false else (r := Some(a); true)
  | (a                   , Ty_Uni(r)           ) ->
      if ty_uvar_occurs r a then false else (r := Some(a); true)
  | (_                   , _                   ) -> false

(* Evaluation *)
and rewrite : sign -> te_ex -> te_ex = fun si t ->
  match pattern_data t with
  | None      -> t
  | Some(s,i) ->
      let rs = find_rules s i si in
      let ts = List.rev_map (fun (i,r) -> match_term si i r t) rs in
      let ts = from_opt_rev ts in
      match ts with
      | []    -> t
      | [t]   -> rewrite si t
      | t::ts ->
          let nb = List.length ts in
          Printf.eprintf "(WARN) %i other rules apply...\n%!" nb;
          rewrite si t

and match_term : sign -> int -> rule -> te_ex -> te_ex option =
  fun si e r t ->
  let ar = mbinder_arity r.def in
  let (l,r) = msubst r.def (Array.init ar (fun _ -> Te_Uni(ref None))) in
  let (t,args) = remove_args t e in
  if eq_te_ex ~no_eval:true si t l then Some(add_args r args) else None

and eval : sign -> te_ex -> te_ex = fun si t ->
  match rewrite si (unfold_te t) with
  | Te_App(t,u) ->
      let t = eval si t in
      let u = eval si u in
      begin
        match t with
        | Te_Abs(f) -> eval si (subst f u)
        | _         ->
            (* FIXME looks hackish... *)
            let t1 = Te_App(t, u) in
            let t2 = rewrite si t1 in
            if t1 == t2 then t1 else eval si t2
      end
  | t           -> t

(* Judgements *)
let rec has_type : sign -> ctxt -> te_ex -> ty_ex -> bool =
  fun si ctx t c ->
    let t = unfold_te t in
    let c = unfold_ty c in
    if !debug then Printf.printf "⊢ %a : %a\n%!" print_te t print_ty c;
    match t with
    (* Variable *)
    | Te_Var(x)     -> subtype si ctx t (find x ctx) c
    (* Witness *)
    | Te_Wit(_,a,_) -> subtype si ctx t a c
    (* Symbol *)
    | Te_Sym(s)     -> subtype si ctx t (SMap.find s si.te_symbols) c
    (* Abstraction *)
    | Te_Abs(f)     ->
        let a = Ty_Uni(ref None) in
        let b = Ty_Uni(ref None) in
        subtype si ctx t (Ty_Fun(a,b)) c
        && has_type si ctx (subst f (Te_Wit(f,a,b))) b
    (* Application *)
    | Te_App(t,u)   ->
        let a = Ty_Uni(ref None) in
        has_type si ctx u a
        && has_type si ctx t (Ty_Fun(a,c))
    (* Illegal stuff *)
    | Te_Uni(_)     -> assert false
    | Te_UWt(_,_)   -> assert false

and subtype : sign -> ctxt -> te_ex -> ty_ex -> ty_ex -> bool =
  fun si ctx t a b ->
    let t = unfold_te t in
    let a = unfold_ty a in
    let b = unfold_ty b in
    if !debug then
      Printf.printf "⊢ %a : %a ⊂ %a\n%!" print_te t print_ty a print_ty b;
    match (a,b) with
    (* Reflexivity. *)
    | (a            , b            ) when eq_ty_ex si a b -> true
    (* Right forall. *)
    | (_            , Ty_FA2(f)    ) ->
        subtype si ctx t a (subst f (Ty_UWt(t,f)))
    | (_            , Ty_FA1(f)    ) ->
        subtype si ctx t a (subst f (Te_UWt(t,f)))
    (* Left forall. *)
    | (Ty_FA2(f)    , _            ) ->
        subtype si ctx t (subst f (Ty_Uni(ref None))) b
    | (Ty_FA1(f)    , _            ) ->
        subtype si ctx t (subst f (Te_Uni(ref None))) b
    (* Function.    *)
    | (Ty_Fun(a1,b1), Ty_Fun(a2,b2)) ->
        let f = binder_from_fun "x" (fun x -> Te_App(t, x)) in
        let wit = Te_Wit(f, a2, b2) in
        subtype si ctx (Te_App(t,wit)) b1 b2
        && subtype si ctx wit a2 a1
    (* No rule apply. *)
    | (_            , _            ) -> false

(* Parser for terms *)
type p_te_ex =
  | P_Te_Sym of string
  | P_Te_Abs of string * p_te_ex
  | P_Te_App of p_te_ex * p_te_ex

type p_ty_ex =
  | P_Ty_Sym of string * p_ty_ex list * p_te_ex list
  | P_Ty_Fun of p_ty_ex * p_ty_ex
  | P_Ty_FA2 of string * p_ty_ex
  | P_Ty_FA1 of string * p_ty_ex

let parser lident = id:''[a-z][a-zA-Z]*''
let parser uident = id:''[A-Z][a-zA-Z]*''

let parser p_term (p : [`Full | `Appl | `Atom]) =
  (* Variable *)
  | x:lident
      when p = `Atom
      -> P_Te_Sym(x)
  (* Abstraction *)
  | "λ" x:lident "." t:(p_term `Full)
      when p = `Full
      -> P_Te_Abs(x,t)
  (* Application *)
  | t:(p_term `Appl) u:(p_term `Atom)
      when p = `Appl
      -> P_Te_App(t,u)
  (* Parentheses and coercions *)
  | "(" (p_term `Full) ")" when p = `Atom
  | (p_term `Appl)         when p = `Full
  | (p_term `Atom)         when p = `Appl

let p_term = p_term `Full

(* Parser for types *)
let parser p_type (p : [`Full | `Func | `Atom]) =
  (* Variable *)
  | x:uident (tys,tes):p_type_args
      when p = `Atom
      -> P_Ty_Sym(x,tys,tes)
  (* Function *)
  | a:(p_type `Atom) "⇒" b:(p_type `Func)
      when p = `Func
      -> P_Ty_Fun(a,b)
  (* Second order quantifier *)
  | "∀" x:uident "." a:(p_type `Full)
      when p = `Full
      -> P_Ty_FA2(x,a)
  (* First order quantifier *)
  | "∀" x:lident "." a:(p_type `Full)
      when p = `Full
      -> P_Ty_FA1(x,a)
  (* Parentheses and coercions *)
  | "(" (p_type `Full) ")" when p = `Atom
  | (p_type `Func)         when p = `Full
  | (p_type `Atom)         when p = `Func

and p_type_args =
  | EMPTY
      -> ([], [])
  | "(" ty:(p_type `Full) tys:{"," (p_type `Full)}* tes:{"," p_term}* ")"
      -> (ty::tys, tes)
  | "(" te:p_term tes:{"," p_term}* ")"
      -> ([], te::tes)

let p_type = p_type `Full

(* Toplevel parser *)
type p_item =
  | TySym  of string * int * int
  | TeSym  of string * p_ty_ex
  | Rule   of string list * p_te_ex * p_te_ex
  | Check  of p_te_ex * p_ty_ex
  | Infer  of p_te_ex
  | Eval   of p_te_ex

let parser integer = i:''[0-9]+'' -> int_of_string i

let parser toplevel =
  | x:uident i:integer j:integer             -> TySym(x,i,j)
  | x:lident ":" a:p_type                    -> TeSym(x,a)
  | "[" xs:lident* "]" t:p_term "→" u:p_term -> Rule(xs,t,u)
  | "#CHECK" t:p_term "," a:p_type           -> Check(t,a)
  | "#INFER" t:p_term                        -> Infer(t)
  | "#EVAL"  t:p_term                        -> Eval(t)

let parser full = {l:toplevel "."}*

let blank buf pos =
  let rec fn state prev ((buf0, pos0) as curr) =
    let (c, buf1, pos1) = Input.read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, c) with
    (* Basic blancs. *)
    | (`Ini, ' ' )
    | (`Ini, '\t')
    | (`Ini, '\r')
    | (`Ini, '\n') -> fn `Ini curr next
    (* Comment. *)
    | (`Ini, '/' ) -> fn `Opn curr next
    | (`Opn, '/' ) -> let p = (buf1, Input.line_length buf1) in fn `Ini p p
    (* Other. *)
    | (`Opn, _   ) -> prev
    | (`Ini, _   ) -> curr
  in
  fn `Ini (buf, pos) (buf, pos)

let parse_file : string -> p_item list =
  Earley.(handle_exception (parse_file full blank))

(* Binder construction. *)
type te_vars = (string * te_var) list
type ty_vars = (string * ty_var) list

let to_te_box : ?tevs:te_vars -> sign -> p_te_ex -> te_box =
  fun ?(tevs=[]) si t ->
  let rec build : te_vars -> p_te_ex -> te_box =
    fun tevs t ->
    match t with
    | P_Te_Sym(x)   ->
        begin
          try box_of_var (List.assoc x tevs) with Not_found ->
          if SMap.mem x si.te_symbols then te_sym x
          else failwith ("Unbound variable " ^ x ^ "...")
        end
    | P_Te_Abs(x,t) -> te_abs x (fun xx -> build ((x,xx)::tevs) t)
    | P_Te_App(t,u) -> te_app (build tevs t) (build tevs u)
  in build tevs t

let to_te_ex : sign -> p_te_ex -> te_ex = fun si t ->
  unbox (to_te_box si t)

let to_ty_box : sign -> p_ty_ex -> ty_box = fun si a ->
  let rec build : te_vars -> ty_vars -> p_ty_ex -> ty_box =
    fun tevs tyvs a ->
    match a with
    | P_Ty_Sym(x,tys,tes) ->
        begin
          try
            let res = box_of_var (List.assoc x tyvs) in
            if tys <> [] || tes <> [] then
              failwith ("No argument expected for " ^ x ^ "...");
            res
          with Not_found ->
          try
            let (i,j) = SMap.find x si.ty_symbols in
            if i <> List.length tys || j <> List.length tes then
              failwith ("Arity missmatch for " ^ x ^ "...");
            let tys = List.map (build tevs tyvs) tys in
            let tes = List.map (to_te_box ~tevs si) tes in
            ty_sym x tys tes
          with Not_found -> failwith ("Unbound variable " ^ x ^ "...")
        end
    | P_Ty_Fun(a,b) -> ty_fun (build tevs tyvs a) (build tevs tyvs b)
    | P_Ty_FA2(x,a) -> ty_fa2 x (fun xx -> build tevs ((x,xx)::tyvs) a)
    | P_Ty_FA1(x,a) -> ty_fa1 x (fun xx -> build ((x,xx)::tevs) tyvs a)
  in build [] [] a

let to_ty_ex : sign -> p_ty_ex -> ty_ex = fun si a ->
  unbox (to_ty_box si a)

(* Main function *)
let handle_file : sign -> string -> sign = fun si fname ->
  let handle_item : sign -> p_item -> sign = fun si it ->
    match it with
    | TySym(x,i,j) ->
        if SMap.mem x si.ty_symbols then
          failwith ("Type symbol " ^ x ^ " already defined...");
        Printf.printf "(type) %s %i %i\n%!" x i j;
        {si with ty_symbols = SMap.add x (i,j) si.ty_symbols}
    | TeSym(x,a)   ->
        if SMap.mem x si.te_symbols then
          failwith ("Term symbol " ^ x ^ " already defined...");
        let a = to_ty_ex si a in
        Printf.printf "(term) %s : %a\n%!" x print_ty a;
        {si with te_symbols = SMap.add x a si.te_symbols}
    | Rule(xs,t,u) ->
        let add_tev x tevs = (x, new_var te_mkfree x)::tevs in
        let tevs = List.fold_right add_tev xs [] in
        let xs = Array.of_list (List.map snd tevs) in
        let t = to_te_box ~tevs si t in
        let u = to_te_box ~tevs si u in
        let def = unbox (bind_mvar xs (box_pair t u)) in
        let t = unbox t in
        let u = unbox u in
        begin
          match pattern_data t with
          | None      -> failwith "Not a valid pattern..."
          | Some(x,i) ->
              let rule = {def; symb = x; arity = i} in
              let fn (_,x) = (x, Ty_Uni(ref None)) in
              let ctx = List.map fn tevs in
              let tt = Ty_Uni(ref None) in
              let tu = Ty_Uni(ref None) in
              if not (has_type si ctx t tt) then
                failwith "Cannot infer the type of the left side...";
              if not (has_type si ctx u tu) then
                failwith "Cannot infer the type of the right side...";
              if not (subtype si ctx u tt tu) then
                failwith "Ill-typed rule...";
              {si with rules = rule::si.rules}
        end
    | Check(t,a)   ->
        let t = to_te_ex si t in
        let a = to_ty_ex si a in
        if not (has_type si [] t a) then failwith "(chck) Type error...";
        Printf.printf "(chck) %a : %a\n%!" print_te t print_ty a;
        si
    | Infer(t)     ->
        let t = to_te_ex si t in
        let a = Ty_Uni(ref None) in
        if has_type si [] t a then
          Printf.eprintf "(infr) %a : %a\n%!" print_te t print_ty a
        else
          Printf.eprintf "(infr) %a : UNABLE TO INFER\n%!" print_te t;
        si
    | Eval(t)      ->
        let t = to_te_ex si t in
        let v = eval si t in
        Printf.eprintf "(eval) %a\n%!" print_te v;
        si
  in
  List.fold_left handle_item si (parse_file fname)

(* Run files *)
let _ =
  let si = ref empty_sign in
  for i = 1 to Array.length Sys.argv - 1 do
    si := handle_file !si Sys.argv.(i)
  done

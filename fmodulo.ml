open Bindlib

let debug = ref true

let from_opt_rev : 'a option list -> 'a list = fun l ->
  let fn acc e =
    match e with
    | None   -> acc
    | Some e -> e::acc
  in
  List.fold_left fn [] l

(* AST *)
type te_expr =
  | Te_Var of te_expr var
  | Te_Sym of string
  | Te_Abs of (te_expr, te_expr) binder
  | Te_App of te_expr * te_expr
  | Te_Uni of te_expr option ref

type ty_expr =
  | Ty_Var of ty_expr var
  | Ty_Sym of string * ty_expr list * te_expr list
  | Ty_Fun of ty_expr * ty_expr
  | Ty_FA2 of (ty_expr, ty_expr) binder
  | Ty_FA1 of (te_expr, ty_expr) binder
  | Ty_Uni of ty_expr option ref

type te_box = te_expr bindbox
type te_var = te_expr var

type ty_box = ty_expr bindbox
type ty_var = ty_expr var

type rule =
  { def   : (te_expr, te_expr * te_expr) mbinder
  ; symb  : string
  ; arity : int }

let rec unfold_te : te_expr -> te_expr = fun t ->
  match t with
  | Te_Uni(r) -> (match !r with None -> t | Some t -> unfold_te t)
  | _         -> t

let rec unfold_ty : ty_expr -> ty_expr = fun a ->
  match a with
  | Ty_Uni(r) -> (match !r with None -> a | Some a -> unfold_ty a)
  | _         -> a

(* Bindlib's "mkfree" *)
let te_mkfree : te_var -> te_expr =
  fun x -> Te_Var(x)

let ty_mkfree : ty_var -> ty_expr =
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
let rec print_te : out_channel -> te_expr -> unit = fun oc t ->
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
  match t with
  | Te_Var(x)   -> output_string oc (name_of x)
  | Te_Sym(s)   -> output_string oc s
  | Te_Abs(b)   ->
      let (x,t) = unbind te_mkfree b in
      Printf.fprintf oc "λ%s.%a" (name_of x) print_te t
  | Te_App(t,u) ->
      let (l1,r1) = if is_abs t then ("(",")") else ("","") in
      let (l2,r2) = if is_app u then ("(",")") else ("","") in
      Printf.fprintf oc "%s%a%s %s%a%s" l1 print_te t r1 l2 print_te u r2
  | Te_Uni(r)   ->
      begin
        match !r with
        | None    -> output_string oc "?"
        | Some(t) -> print_te oc t
      end

let rec print_ty : out_channel -> ty_expr -> unit = fun oc a ->
  let rec is_atom a =
    match a with
    | Ty_Var(_)     -> true
    | Ty_Sym(_,_,_) -> true
    | Ty_Uni(r)     -> (match !r with None -> false | Some a -> is_atom a)
    | _             -> false
  in
  match a with
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
  | Ty_Uni(r)         ->
      begin
        match !r with
        | None    -> output_string oc "?"
        | Some(a) -> print_ty oc a
      end

(* Pattern data *)
let pattern_data : te_expr -> (string * int) option = fun t ->
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
  { te_symbols : ty_expr SMap.t
  ; ty_symbols : (int * int) SMap.t
  ; rules      : rule list }

let empty_sign =
  { te_symbols = SMap.empty
  ; ty_symbols = SMap.empty
  ; rules = [] }

type ctxt = (te_var * ty_expr) list

let find : te_var -> ctxt -> ty_expr = fun x ctx ->
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

let remove_args : te_expr -> int -> te_expr * te_expr list = fun t n ->
  let rec rem acc n t =
    assert (n >= 0);
    match (t, n) with
    | (_          , 0) -> (t, acc)
    | (Te_App(t,u), n) -> rem (u::acc) (n-1) t
    | (_          , _) -> assert false
  in
  rem [] n t

let add_args : te_expr -> te_expr list -> te_expr =
  List.fold_left (fun t u -> Te_App(t,u))

(* Equality *)
let rec eq_te_expr : ?no_eval:bool -> sign -> te_expr -> te_expr -> bool =
  fun ?(no_eval=false) si t u ->
  let eq_binders b1 b2 =
    let x = free_of (new_var te_mkfree "<dummy>") in
    eq_te_expr ~no_eval si (subst b1 x) (subst b2 x)
  in
  let t = if no_eval then t else eval si t in
  let u = if no_eval then u else eval si u in
  match (unfold_te t, unfold_te u) with
  | (Te_Var(x1)   , Te_Var(x2)   ) -> eq_vars x1 x2
  | (Te_Sym(s1)   , Te_Sym(s2)   ) -> s1 = s2
  | (Te_Abs(b1)   , Te_Abs(b2)   ) -> eq_binders b1 b2
  | (Te_App(t1,u1), Te_App(t2,u2)) -> eq_te_expr ~no_eval si t1 t2
                                      && eq_te_expr ~no_eval si u1 u2
  | (Te_Uni(r)    , t            ) -> r := Some(t); true
  | (t            , Te_Uni(r)    ) -> r := Some(t); true
  | (_            , _            ) -> false

and eq_ty_expr : sign -> ty_expr -> ty_expr -> bool = fun si a b ->
  match (unfold_ty a, unfold_ty b) with
  | (Ty_Var(x1)          , Ty_Var(x2)          ) -> eq_vars x1 x2
  | (Ty_Sym(s1,tys1,tes1), Ty_Sym(s2,tys2,tes2)) ->
      assert (List.length tys1 = List.length tys2);
      assert (List.length tes1 = List.length tes2);
      s1 = s2 && List.for_all2 (eq_ty_expr si) tys1 tys2
      && List.for_all2 (eq_te_expr si) tes1 tes2
  | (Ty_Fun(a1,b1)       , Ty_Fun(a2,b2)       ) ->
      eq_ty_expr si a1 a2 && eq_ty_expr si b1 b2
  | (Ty_FA2(b1)          , Ty_FA2(b2)          ) ->
      let x = free_of (new_var ty_mkfree "<dummy>") in
      eq_ty_expr si (subst b1 x) (subst b2 x)
  | (Ty_FA1(b1)          , Ty_FA1(b2)          ) ->
      let x = free_of (new_var te_mkfree "<dummy>") in
      eq_ty_expr si (subst b1 x) (subst b2 x)
  | (Ty_Uni(r)           , a                   ) -> r := Some(a); true
  | (a                   , Ty_Uni(r)           ) -> r := Some(a); true
  | (_                   , _                   ) -> false

(* Evaluation *)
and rewrite : sign -> te_expr -> te_expr = fun si t ->
  match pattern_data t with
  | None      -> t
  | Some(s,i) ->
      let rs = find_rules s i si in
      let ts = List.rev_map (fun (i,r) -> match_term si i r t) rs in
      let ts = from_opt_rev ts in
      match ts with
      | []    -> t
      | [t]   -> t
      | t::ts ->
          let nb = List.length ts in
          Printf.eprintf "(WARN) %i other rules apply...\n%!" nb; t

and match_term : sign -> int -> rule -> te_expr -> te_expr option =
  fun si e r t ->
  let ar = mbinder_arity r.def in
  let (l,r) = msubst r.def (Array.init ar (fun _ -> Te_Uni(ref None))) in
  let (t,args) = remove_args t e in
  if eq_te_expr ~no_eval:true si t l then Some(add_args r args) else None

and eval : sign -> te_expr -> te_expr = fun si t ->
  let t = rewrite si t in
  match t with
  | Te_App(t,u) ->
      begin
        match t with
        | Te_Abs(f) -> eval si (subst f u)
        | t         -> Te_App(t, u)
      end
  | _           -> t

(* Judgements *)
let rec infer : sign -> ?ctx:ctxt -> te_expr -> ty_expr =
  fun si ?(ctx=[]) t ->
  if !debug then Printf.printf "INF %a\n%!" print_te t;
  match t with
  | Te_Var(x)   -> find x ctx
  | Te_Sym(s)   -> SMap.find s si.te_symbols
  | Te_Abs(b)   ->
      let (x,t) = unbind te_mkfree b in
      let a = Ty_Uni(ref None) in
      let b = infer si ~ctx:((x,a)::ctx) t in
      Ty_Fun(a,b)
  | Te_App(t,u) ->
      begin
        match infer si ~ctx t with
        | Ty_Fun(a,b) -> if has_type si ~ctx u a then b else raise Not_found
        | _           -> raise Not_found
      end
  | Te_Uni(r)   ->
      begin
        match !r with 
        | None    -> assert false (* Should not happen. *)
        | Some(t) -> infer si ~ctx t
      end

and  has_type : sign -> ?ctx:ctxt -> te_expr -> ty_expr -> bool =
  fun si ?(ctx=[]) t a ->
  if !debug then
    Printf.printf "%a ⊢ %a : %a\n%!" print_ctxt ctx print_te t print_ty a;
  match (t, unfold_ty a) with
  (* Variable *)
  | (Te_Var(x)  , a          ) ->
      eq_ty_expr si (find x ctx) a
  (* Symbol *)
  | (Te_Sym(s)  , a          ) ->
      eq_ty_expr si (SMap.find s si.te_symbols) a
  (* Abstraction *)
  | (Te_Abs(_)  , Ty_Uni(r)  ) ->
      r := Some (Ty_Fun(Ty_Uni(ref None), Ty_Uni(ref None)));
      has_type si ~ctx t a
  | (Te_Abs(f)  , Ty_Fun(a,b)) ->
      let (x,t) = unbind te_mkfree f in
      has_type si ~ctx:((x,a)::ctx) t b
  (* Application *)
  | (Te_App(t,u), b          ) ->
      let a = infer si ~ctx u in
      has_type si ~ctx t (Ty_Fun(a,b))
  (* No rule apply. *)
  | (_          , _          ) ->
      failwith "No rule apply..."

(* Parser for terms *)
type p_te_expr =
  | P_Te_Sym of string
  | P_Te_Abs of string * p_te_expr
  | P_Te_App of p_te_expr * p_te_expr

type p_ty_expr =
  | P_Ty_Sym of string * p_ty_expr list * p_te_expr list
  | P_Ty_Fun of p_ty_expr * p_ty_expr
  | P_Ty_FA2 of string * p_ty_expr
  | P_Ty_FA1 of string * p_ty_expr

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
  | TeSym  of string * p_ty_expr
  | Rule   of string list * p_te_expr * p_te_expr
  | Check  of p_te_expr * p_ty_expr
  | Infer  of p_te_expr
  | Eval   of p_te_expr

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

let to_te_box : ?tevs:te_vars -> sign -> p_te_expr -> te_box =
  fun ?(tevs=[]) si t ->
  let rec build : te_vars -> p_te_expr -> te_box =
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

let to_te_expr : sign -> p_te_expr -> te_expr = fun si t ->
  unbox (to_te_box si t)

let to_ty_box : sign -> p_ty_expr -> ty_box = fun si a ->
  let rec build : te_vars -> ty_vars -> p_ty_expr -> ty_box =
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

let to_ty_expr : sign -> p_ty_expr -> ty_expr = fun si a ->
  unbox (to_ty_box si a)

(* Main function *)
let handle_file : sign -> string -> sign = fun si fname ->
  let handle_item : sign -> p_item -> sign = fun si it ->
    match it with
    | TySym(x,i,j) ->
        if SMap.mem x si.ty_symbols then
          failwith ("Type symbol " ^ x ^ " already defined...");
        Printf.printf "(type) %s(%i,%i)\n%!" x i j;
        {si with ty_symbols = SMap.add x (i,j) si.ty_symbols}
    | TeSym(x,a)   ->
        if SMap.mem x si.te_symbols then
          failwith ("Term symbol " ^ x ^ " already defined...");
        let a = to_ty_expr si a in
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
              try
                let fn (_,x) = (x, Ty_Uni(ref None)) in
                let ctx = List.map fn tevs in
                let tt = infer si ~ctx t in
                let tu = infer si ~ctx u in
                if not (eq_ty_expr si tt tu) then raise Not_found;
                {si with rules = rule::si.rules}
              with Not_found -> failwith "Ill-typed rule..."
        end
    | Check(t,a)   ->
        let t = to_te_expr si t in
        let a = to_ty_expr si a in
        if not (has_type si t a) then failwith "(chck) Type error...";
        Printf.printf "(chck) %a : %a\n%!" print_te t print_ty a;
        si
    | Infer(t)     ->
        let t = to_te_expr si t in
        begin
          try
            let a = infer si t in
            Printf.eprintf "(infr) %a : %a\n%!" print_te t print_ty a
          with Not_found ->
            Printf.eprintf "(infr) %a : UNABLE TO INFER\n%!" print_te t
        end;
        si
    | Eval(t)      ->
        let t = to_te_expr si t in
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

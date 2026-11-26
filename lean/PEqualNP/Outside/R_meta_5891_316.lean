import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 50000 in
set_option synthInstance.maxSize 2048 in
theorem PEqualNP.Outside.R_meta_5891_316
    (localGrids : ∃ (E : Circuit) (e : ℕ) (C : Bool → Circuit) (q : Bool → ℕ),
      MetaComplexity.Monotone2 E ∧ E.size ≤ 2 ∧ E.output < 9+E.size ∧ e < 9+E.size ∧
      E.size + (C false).size + (C true).size ≤ 58 ∧
      ∀ b, MetaComplexity.Monotone2 (C b) ∧ (C b).output < 19+(C b).size ∧
        q b < 19+(C b).size ∧ ∀ x : Fin 17 → Bool,
        let h := fun (i j : Fin 17) =>
          let u := (j.val-6)/3
          let v := (j.val-6)%3
          i.val < 6 ∧ (j.val = 15+i.val/3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
            (if b then (u+(if i.val<3 then 2*v else v))%3 else
              (if i.val<3 then u else v)) = i.val%3))
        let t := E.wires (((List.ofFn x).drop 6).take 9)
        let z := List.ofFn x ++ [t.getD E.output false,t.getD e false]
        ((C b).eval z = true ↔ ∃ i j, h i j ∧ x i = true ∧ x j = true) ∧
        ((C b).eval z = false → ((C b).wires z).getD (q b) false = (x 15 || x 16)))
    (appendCircuit : ∀ (m n : ℕ) (B C : Circuit) (q : ℕ) (f : Fin n → ℕ),
      MetaComplexity.Monotone2 B → MetaComplexity.Monotone2 C →
      C.output < n+C.size → q < n+C.size → (∀ i, f i < m+B.size) →
      ∃ (D : Circuit) (r : ℕ), MetaComplexity.Monotone2 D ∧ D.size = B.size+C.size ∧
        D.output < m+D.size ∧ r < m+D.size ∧ ∀ x : Fin m → Bool,
        let y := List.ofFn x
        let z := List.ofFn (fun i => (B.wires y).getD (f i) false)
        D.eval y = C.eval z ∧ (D.wires y).getD r false = (C.wires z).getD q false ∧
        ∀ k < m+B.size, (D.wires y).getD k false = (B.wires y).getD k false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (60 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let H (b : Bool) (i j : Fin 17) :=
    let u := (j.val-6)/3
    let v := (j.val-6)%3
    i.val < 6 ∧ (j.val = 15+i.val/3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
      (if b then (u+(if i.val<3 then 2*v else v))%3 else
        (if i.val<3 then u else v)) = i.val%3))
  let full := fun (i j : Fin 25) =>
    i.val < 12 ∧ 12 ≤ j.val ∧ (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ)
  let f (b : Bool) : Fin 17 → Fin 25 := if b then
    ![9,10,5,3,4,6,24,20,14,23,18,22,19,17,16,15,21] else
    ![0,2,8,1,7,11,24,20,14,23,18,22,19,17,16,12,13]
  let cells : Fin 9 → Fin 25 := ![24,20,14,23,18,22,19,17,16]
  have liftEdge : ∀ b i j, H b i j → full (f b i) (f b j) := by decide +kernel
  have cover : ∀ i j, full i j → ∃ b a d, H b a d ∧ f b a = i ∧ f b d = j := by decide +kernel
  let hit (b : Bool) (x : Fin 25 → Bool) :=
    ∃ i j, H b i j ∧ x (f b i) = true ∧ x (f b j) = true
  have parts (x : Fin 25 → Bool) :
      (∃ i j, full i j ∧ x i = true ∧ x j = true) ↔ hit false x ∨ hit true x := by
    constructor
    · rintro ⟨i,j,h,xi,xj⟩
      obtain ⟨b,a,d,ad,rfl,rfl⟩ := cover i j h
      cases b
      · exact Or.inl ⟨_,_,ad,xi,xj⟩
      · exact Or.inr ⟨_,_,ad,xi,xj⟩
    · rintro (⟨a,d,ad,xa,xd⟩|⟨a,d,ad,xa,xd⟩)
      · exact ⟨_,_,liftEdge false _ _ ad,xa,xd⟩
      · exact ⟨_,_,liftEdge true _ _ ad,xa,xd⟩
  have common (b : Bool) (x : Fin 25 → Bool) :
      ((List.ofFn (x ∘ f b)).drop 6).take 9 = List.ofFn (x ∘ cells) := by cases b <;> rfl
  obtain ⟨E,e,C,q,em,es,eo,er,budget,loc⟩ := localGrids
  let empty : Circuit := ⟨[],0⟩
  have emptyMono : MetaComplexity.Monotone2 empty := by intro g hg; cases hg
  have emp : empty.size = 0 := rfl
  have rd (x : Fin 25 → Bool) (i : Fin 25) : (empty.wires (List.ofFn x)).getD i.val false = x i := by
    change (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  obtain ⟨P,t,pm,ps,po,pt,pe⟩ := appendCircuit 25 9 empty E e (fun i => (cells i).val)
    emptyMono em eo er (by intro i; simpa [emp] using (cells i).isLt)
  let payload (b : Bool) (x : Fin 25 → Bool) :=
    let a := E.wires (List.ofFn (x ∘ cells))
    List.ofFn (x ∘ f b) ++ [a.getD E.output false,a.getD e false]
  let route (b : Bool) : Fin 19 → ℕ := Fin.append (fun i => (f b i).val) ![P.output,t]
  have routeBound (b : Bool) (i : Fin 19) : route b i < 25+P.size := by
    have h (j : Fin 17) : (f b j).val < 25+P.size := by
      have := (f b j).isLt
      omega
    fin_cases i <;> first | exact h _ | exact po | exact pt
  have peval (x : Fin 25 → Bool) :
      (P.wires (List.ofFn x)).getD P.output false = E.eval (List.ofFn (x ∘ cells)) ∧
      (P.wires (List.ofFn x)).getD t false = (E.wires (List.ofFn (x ∘ cells))).getD e false ∧
      ∀ i : Fin 25, (P.wires (List.ofFn x)).getD i.val false = x i := by
    obtain ⟨a,b,c⟩ := pe x
    have env : (fun i => (empty.wires (List.ofFn x)).getD (cells i).val false) = x ∘ cells :=
      funext (fun i => rd x (cells i))
    rw [env] at a b
    exact ⟨a,b,fun i => (c i.val (by simpa [emp] using i.isLt)).trans (rd x i)⟩
  have payloadAt (b : Bool) (x : Fin 25 → Bool) :
      List.ofFn (fun i => (P.wires (List.ofFn x)).getD (route b i) false) = payload b x := by
    obtain ⟨one,two,raw⟩ := peval x
    let w := E.wires (List.ofFn (x ∘ cells))
    have form : List.ofFn (Fin.append (x ∘ f b) ![w.getD E.output false,w.getD e false]) =
        payload b x := by rw [List.ofFn_fin_append]; rfl
    rw [← form]
    apply congrArg List.ofFn
    funext i
    fin_cases i <;> first | exact raw _ | exact one | exact two
  obtain ⟨cm0,co0,ct0,loc0⟩ := loc false
  obtain ⟨cm1,co1,ct1,loc1⟩ := loc true
  obtain ⟨A,r,am,asz,ao,ar,ae⟩ := appendCircuit 25 19 P (C false) (q false)
    (route false) pm cm0 co0 ct0 (routeBound false)
  obtain ⟨B,s,bm,bsz,bo,bs,be⟩ := appendCircuit 25 19 A (C true) (q true)
    (route true) am cm1 co1 ct1 (by intro i; have := routeBound true i; omega)
  let joins : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[2,3]⟩],4⟩
  have jm : MetaComplexity.Monotone2 joins := by
    intro k h
    change k ∈ [_,_] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> simp
  let endMap : Fin 4 → ℕ := ![A.output,B.output,r,s]
  obtain ⟨D,w,dm,dsz,dout,dw,de⟩ := appendCircuit 25 4 B joins 5 endMap bm jm
    (by decide +kernel) (by decide +kernel) (by intro i; fin_cases i <;> dsimp [endMap] <;> omega)
  have sj : joins.size = 2 := rfl
  refine ⟨D,w,dm,by omega,dout,dw,?_⟩
  intro x
  obtain ⟨aout,atap,akeep⟩ := ae x
  rw [payloadAt] at aout atap
  obtain ⟨bout,btap,bkeep⟩ := be x
  have aft : List.ofFn (fun i => (A.wires (List.ofFn x)).getD (route true i) false) = payload true x := by
    rw [← payloadAt]
    exact congrArg List.ofFn (funext (fun i => akeep (route true i) (routeBound true i)))
  rw [aft] at bout btap
  obtain ⟨out,tag,_⟩ := de x
  let v := fun (k : ℕ) => (B.wires (List.ofFn x)).getD k false
  have eval1 : joins.eval (List.ofFn (fun i => v (endMap i))) = (v A.output || v B.output) := by
    change (v A.output || (v B.output || false)) = _
    simp
  have eval2 : (joins.wires (List.ofFn (fun i => v (endMap i)))).getD 5 false = (v r || v s) := by
    change (v r || (v s || false)) = _
    simp
  rw [eval1] at out
  rw [eval2] at tag
  change D.eval _ = ((B.wires _).getD A.output false || B.eval _) at out
  change (D.wires _).getD w false = ((B.wires _).getD r false || (B.wires _).getD s false) at tag
  rw [bkeep _ ao] at out
  change D.eval _ = (A.eval _ || B.eval _) at out
  rw [aout,bout] at out
  rw [bkeep _ ar,atap,btap] at tag
  obtain ⟨good0,aux0⟩ := loc0 (x ∘ f false)
  obtain ⟨good1,aux1⟩ := loc1 (x ∘ f true)
  rw [common] at good0 aux0 good1 aux1
  change (D.eval _ = true ↔ ∃ i j, full i j ∧ x i = true ∧ x j = true) ∧ _
  constructor
  · rw [out,Bool.or_eq_true]
    exact (or_congr good0 good1).trans (parts x).symm
  · intro zero
    rw [out,Bool.or_eq_false_iff] at zero
    rw [tag,aux0 zero.1,aux1 zero.2]
    change ((x 12 || x 13) || (x 15 || x 21)) = _
    simp only [Bool.or_assoc]

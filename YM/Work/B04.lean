import YM.Bid.Phase

/-!
# Flash pair: grid passage

Keep the shift `D t j` outside the ordinary theta action (on the reflected
plants too). Expand into point moments on this same Wilson family; the point
passage is on the appended grid (eventually generic). First fix `i,j` and
sufficiently large `t`, *then* take ordered tails.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B04
open Set Filter Function MeasureTheory OS Table Word Extraction Lattice Wilson
open scoped Topology BigOperators

private def D (t i : ℕ) : Cover := fun _ => (t : ℤ)*i

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} {n m : ℕ} {k : ℕ}

private lemma gridPoint_add (s : Schedule) (k : ℕ) (x u : Cover) :
    s.gridPoint k (x+u) = s.gridPoint k x + s.gridPoint k u := by
  ext a
  simp [Schedule.gridPoint, mul_add]

private lemma grid_spin (x : Fin n → Cover) (s : Signed) :
    Points.move s.ortho (Order.grid C k x) = Order.grid C k (s.act ∘ x) := by
  ext1 i; ext a
  obtain ⟨b,rfl⟩ := s.perm.surjective a
  simp [Order.grid,Schedule.gridPoint,Signed.ortho_move]

private lemma eventually_pair {x : Fin n → Cover} {y : Fin m → Cover}
    (hx : Order.grid C k x ∈ generic n) (hy : Order.grid C k y ∈ generic m)
    (i j : ℕ) (hij : i < j) :
    ∀ᶠ t : ℕ in atTop,
      Order.grid C k (Fin.append (fun b => x b + D t i) (fun c => y c + D t j)) ∈ generic (n+m) := by
  have sep (a : Axis) (b : Fin n) (c : Fin m) :
      ∀ᶠ t : ℕ in atTop,
        C.S.gridPoint k (x b + D t i) a < C.S.gridPoint k (y c + D t j) a := by
    let g := C.S.a k*((j:ℝ)-(i:ℝ))
    have h : Tendsto (fun t : ℕ => (t:ℝ)*g) atTop atTop :=
      Tendsto.atTop_mul_const
        (mul_pos (C.S.a_pos k) (sub_pos.mpr (by exact_mod_cast hij))) tendsto_natCast_atTop_atTop
    filter_upwards [h.eventually (eventually_gt_atTop (C.S.gridPoint k (x b) a - C.S.gridPoint k (y c) a))] with t ht
    simp [Schedule.gridPoint,D,g] at ht ⊢
    linarith
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr fun b => eventually_all.mpr (sep a b)] with t h
  intro a b c he
  revert he
  refine Fin.addCases ?_ ?_ b
  · intro b
    refine Fin.addCases ?_ ?_ c
    · intro c he
      simp [Order.grid,gridPoint_add] at he
      rw [hx a (show _ from he)]
    intro c he
    exfalso
    exact (h a b c).ne (by simpa [Order.grid] using he)
  intro b
  refine Fin.addCases ?_ ?_ c
  · intro c he
    exfalso
    exact (h a c b).ne' (by simpa [Order.grid] using he)
  intro c he
  simp [Order.grid,gridPoint_add] at he
  rw [hy a (show _ from he)]

private lemma anti_grid (v : Fin n → C.book.Token) (x : Fin n → Cover) :
    Grid.anti (Grid.Tag k v x) =
      Grid.Tag (C:=C) k (C.book.move (Signed.mirror timeAxis) ∘ v)
        ((Signed.mirror timeAxis).act ∘ x) := by
  unfold Grid.anti Word.act Grid.Tag Word.realize
  rw [← grid_spin x, List.map_ofFn]
  rfl

private lemma tag_pair (v : Fin n → C.book.Token) (w : Fin m → C.book.Token)
    (x : Fin n → Cover) (y : Fin m → Cover) (i j t : ℕ) :
    carry (Grid.Tag k v x) (Grid.force (C:=C) k t i) ++
        carry (Grid.Tag k w y) (Grid.force (C:=C) k t j)
      = Grid.Tag (C:=C) k (Fin.append v w)
          (Fin.append (fun b => x b + D t i) (fun c => y c + D t j)) := by
  unfold carry Grid.Tag Word.realize
  rw [List.map_ofFn,List.map_ofFn,← List.ofFn_fin_append]
  congr 1
  funext b
  refine Fin.addCases ?_ ?_ b
  · intro b; simp [Order.grid,gridPoint_add,Grid.force]; rfl
  intro b; simp [Order.grid,gridPoint_add,Grid.force]; rfl

private def term (k : ℕ) (v : Fin n → C.book.Token) (w : Fin m → C.book.Token)
    (x : Fin n → Cover) (y : Fin m → Cover) (i j t N p : ℕ) :=
  ∫ U : Config G (C.side N p),
    (Grid.tiny k v x N p (D t i) U * Grid.tiny k w y N p (D t j) U).re
      ∂law G _ (C.beta N p)

private lemma tiny_mul (v : Fin n → C.book.Token) (w : Fin m → C.book.Token)
    (x : Fin n → Cover) (y : Fin m → Cover) (u z : Cover) (N p : ℕ) :
    (fun U => Grid.tiny k v x N p u U * Grid.tiny k w y N p z U) =
    fun U => ∏ a : Fin (n+m), C.seen (Fin.append v w a)
      (Cells.location C.S k N p (Fin.append (fun b => x b + u) (fun c => y c + z) a)) U := by
  funext U
  simp only [Grid.tiny, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

private lemma tiny_integrable (v : Fin n → C.book.Token) (w : Fin m → C.book.Token)
    (x : Fin n → Cover) (y : Fin m → Cover) (u z : Cover) (k N p : ℕ) :
    Integrable (fun U => Grid.tiny k v x N p u U * Grid.tiny k w y N p z U)
      (law G _ (C.beta N p)) := by
  rw [tiny_mul]
  apply Family.integrableR

private lemma term_num (v : Fin n → C.book.Token) (w : Fin m → C.book.Token)
    (x : Fin n → Cover) (y : Fin m → Cover) (k i j t N p : ℕ) :
    term k v w x y i j t N p =
      (C.numeric N p (Fin.append v w)
        (fun a => Cells.location C.S k N p
          (Fin.append (fun b => x b + D t i) (fun c => y c + D t j) a))).re := by
  calc
    _ = (∫ U, Grid.tiny k v x N p (D t i) U * Grid.tiny k w y N p (D t j) U ∂law G _ (C.beta N p)).re :=
      integral_re (tiny_integrable v w x y _ _ k N p)
    _ = _ := by rw [tiny_mul, C.num]

private lemma term_limit (H : F.PointLimits C S)
    (v : Fin n → C.book.Token) (w : Fin m → C.book.Token) (x : Fin n → Cover) (y : Fin m → Cover)
    (hx : Order.grid C k x ∈ generic n) (hy : Order.grid C k y ∈ generic m)
    (i j : ℕ) (hij : i < j) :
    ∀ᶠ t : ℕ in atTop,
      Tendsto (fun u : ℕ × ℕ => term k v w x y i j t u.1 u.2) F.fuse
        (𝓝 (Grid.compareA (S:=S) k t i j (Grid.Tag k v x) (Grid.Tag k w y)).re) := by
  filter_upwards [eventually_pair hx hy i j hij] with t ht
  simp_rw [term_num]
  unfold Grid.compareA
  rw [tag_pair]
  unfold Grid.Tag
  rw [Table.readAt]
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (Order.inPatch H k (Fin.append _ _) ht (Fin.append v w))

private lemma bill_terms (v : Fin n → C.book.Token) (x : Fin n → Cover) (k i j t N p : ℕ) :
    let v' := C.book.move (Signed.mirror timeAxis) ∘ v
    let x' : Fin n → Cover := (Signed.mirror timeAxis).act ∘ x
    Grid.bill k v x i j N p t =
      (term k v v x x i j t N p - term k v v' x x' i j t N p) -
      (term k v' v x' x i j t N p - term k v' v' x' x' i j t N p) := by
  intro v' x'
  let A (i : ℕ) := Grid.tiny k v x N p (D t i)
  let B (i : ℕ) := Grid.tiny k v' x' N p (D t i)
  let μ := law G (C.side N p) (C.beta N p)
  have haa : Integrable (fun U => (A i U * A j U).re) μ :=
    (tiny_integrable v v x x _ _ k N p).re
  have hab : Integrable (fun U => (A i U * B j U).re) μ :=
    (tiny_integrable v v' x x' _ _ k N p).re
  have hba : Integrable (fun U => (B i U * A j U).re) μ :=
    (tiny_integrable v' v x' x _ _ k N p).re
  have hbb : Integrable (fun U => (B i U * B j U).re) μ :=
    (tiny_integrable v' v' x' x' _ _ k N p).re
  have ha : Integrable (fun U => (A i U * A j U).re - (A i U * B j U).re) μ := haa.sub hab
  have hb : Integrable (fun U => (B i U * A j U).re - (B i U * B j U).re) μ := hba.sub hbb
  change
    (∫ U, ((A i U - B i U) * (A j U - B j U)).re ∂μ) =
    ((∫ U, (A i U * A j U).re ∂μ)-(∫ U, (A i U * B j U).re ∂μ)) -
    ((∫ U, (B i U * A j U).re ∂μ)-(∫ U, (B i U * B j U).re ∂μ))
  simp_rw [sub_mul, mul_sub, Complex.sub_re]
  rw [integral_sub ha hb, integral_sub haa hab, integral_sub hba hbb]



theorem answer : YM.Bid.B04 := by
  intro G C S F n v x k _ _ H _ hx i j hij
  let s := Signed.mirror timeAxis
  let v' := C.book.move s ∘ v
  let x' : Fin n → Cover := s.act ∘ x
  have hs : Order.grid C k x' ∈ generic n := grid_spin x s ▸ Order.mirrorG s hx
  filter_upwards [term_limit H v v x x hx hx i j hij, term_limit H v v' x x' hx hs i j hij,
    term_limit H v' v x' x hs hx i j hij, term_limit H v' v' x' x' hs hs i j hij] with t haa hab hba hbb
  simp_rw [Grid.event, anti_grid, bill_terms]
  exact (haa.sub hab).sub (hba.sub hbb)

-- Edge check: no slots, no tail assumptions.
example (k : ℕ) (v : Fin 0 → C.book.Token) (x : Fin 0 → Cover) :
    Grid.Expects (S:=S) (f:=F) k v x := by
  intro i j _
  filter_upwards with t
  simp [Grid.bill,Grid.flash,Grid.tiny,Grid.event,Grid.compareA,Grid.Tag,
    Word.realize, Grid.anti, Word.act]

end YM.Work.B04

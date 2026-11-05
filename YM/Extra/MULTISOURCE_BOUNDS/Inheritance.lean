import YM.Extra.MULTISOURCE_BOUNDS.SystemPrices

/-!
# Additional vacuum receipt towards System.Forward

Projected-variant hit sums from `C.Makes`'s **actual** E and K budgets,
including arbitrary post-L powers of B and the monitor, and one optional
inflation for K even by the old **square root** divisor. These are geometric
and kernel-input estimates. No claim that all unmarked vertices also involving
packet/trigger/loop data cost only these weights (or are exhausted by the
families tested here). Identifies one way to bid for the extra thresholds
before calling `System.price`. The halo test can include e.g. the external
`inspected` reads. See .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.System
open Function Filter Lattice RG RG.Supply Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {C : Family G} {α : Type*}

section Geometry
variable {n m : Side} (q : Ratio m n)

theorem fibers : Occupancy q.parent (q.count.val^4) := fun y => by
  rw [← site_card]; apply Finset.card_le_card_of_injOn q.residue (fun i _ => mem_univ _)
    (fun i hi j hj hh => by rw [← q.unpack_at i,← q.unpack_at j,(mem_filter.mp hi).2, (mem_filter.mp hj).2,hh])

theorem within (X : Support n) : inspected X ⊆ halo 4 X := by
  intro i hi
  obtain h|h := Finset.mem_union.mp hi
  · exact halo_subset _ _ h
  obtain ⟨p,-,hp⟩ := Finset.mem_biUnion.mp h; split at hp
  next => simp at hp
  next hD =>
    obtain ⟨y,hy⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hD
    apply halo_spec.mpr
    refine ⟨y,(mem_inter.mp hy).1,(separation_triangle _ p.1 _).trans ?_⟩
    rw [separation_comm y]; exact Nat.add_le_add (Work.E01.sep_touched _ _ (mem_inter.mp hy).2) (Work.E01.sep_touched _ _ hp)

/-- Project the entire external flag-read halo once. -/
theorem inspected_budget (X : Support n) {B : ℕ} (hB : 0 < B) (k : ℕ) :
    halo (k*B) ((inspected X).image q.parent) ⊆ halo ((k+5)*B) (X.image q.parent) := by
  intro i hi; obtain ⟨j,hj,he⟩ := halo_spec.mp hi; obtain ⟨v,hv,rfl⟩ := mem_image.mp hj
  obtain ⟨u,hu,ht⟩ := halo_spec.mp (within _ hv)
  have hh := Corona.foreshorten q u v; have hz := q.count.property
  have hh' : separation (q.parent u) (q.parent v) ≤ 5 := by
    apply Nat.le_of_mul_le_mul_left ((hh.trans (Nat.add_le_add_right ht _)).trans ?_) hz
    rw [Nat.mul_succ]; gcongr; exact le_mul_of_one_le_left (by decide) (show 1 ≤ q.count.val from hz)
  exact halo_spec.mpr ⟨_,mem_image_of_mem _ hu,(separation_triangle _ _ _).trans ((Nat.add_le_add hh' he).trans
    (by nlinarith only [hB]))⟩
end Geometry

section Prices

abbrev expense (a : Levels G) (s : Scope) (d : ℕ→ℕ) (m : ℕ) := pad ((a.params m).supportExponent+7)
      (a.params (m+1)).supportExponent (s.expand (a.clock.J (m+1))) (d (a.clock.J (m+1)))

/-- Here `d j` power of old cover, `k j` power for `post` at fine βHat. -/
structure Inspect (s : Scope) (d k : ℕ→ℕ) (c : ℕ → ℝ) (a : Levels G) : Prop where
  cost m : let j := a.clock.J (m+1); let x := a.clock.hatBeta m; let y := a.clock.hatBeta (m+1)
    post (k j) (c j) y ≤ y^((1:ℝ)/2) ∧
      siteFactor (a.clock.coverSize m) * ( (a.S.block m).val ^4 * expense a s d m) ≤ x^((1:ℝ)/4)



variable {p N m : ℕ} {s : Scope} {t : Tariff} {c : ℕ→ℝ} {k d : ℕ→ℕ}
variable (hC : C.Makes) (H : Prepared s t C.localSection C.path.levels)
    (I : Inspect s d k c C.path.levels) (hc : ∀ i,0 ≤ c i) (hξ : 7 ≤ s.inflate (year C (m+1)))

structure Variants (X : ℕ → Support (C.side (m+1) p)) (Y : α → Support (C.side m p)) (s : Scope) (d k : ℕ→ℕ)
    (c : ℕ → ℝ) (e : ℕ → ℝ) (g : α→ℝ) : Prop where
  pos i : 0 ≤ g i
  funds : let j := year C (m+1); let q := (C.path.levels.clock.op m p).ratio
    ∃ f : α → ℕ, (∀ i,0<g i → Y i ⊆ halo (s.expand j*(point C m).B) ((X (f i)).image q.parent)) ∧
      ∀ i,SumBudget (fun l => if f l=i then g l else 0) (post (k j) (c j) (hat C (m+1)) *
        (1+(coverNumber (point C (m+1)).B (X i):ℝ))^(d j) * e i)

include H I hc hξ in
lemma Variants.cashed {X : ℕ → Support (C.side (m+1) p)} {Y : α → Support (C.side m p)} {e : ℕ → ℝ} {g : α→ℝ}
    (h : Variants X Y s d k c e g) (hG : G.Simple) (he : ∀ i,0 ≤ e i) (o : ℕ → Site (C.side (m+1) p))
    (ho : ∀ i,o i∈X i) (hB : let P := point C (m+1); Rooted (fun i => {o i}) X P.B P.supportExponent e (hat C (m+1))⁻¹) :
    Ac.Hit Y (point C m).B g ((point C m).supportExponent+6) ((hat C m)^(-(1/4:ℝ))) := by
  obtain ⟨f,hf,hf'⟩ := h.funds
  let q := (C.path.levels.clock.op m p).ratio
  let j := year C (m+1); let P := point C m; let Q := point C (m+1); let A := P.supportExponent+6
  let y := hat C (m+1); let x := hat C m
  let U i := halo (s.expand j*P.B) ((X (f i)).image q.parent)
  let v := post (k j) (c j) y
  have hz : 0 < x := zero_lt_one.trans (C.path.levels.fits.delayed m)
  have hxy : x ≤ y := nearby C m hG
  have hy : 0 < y := hz.trans_le hxy
  have hv : 0 ≤ v := mul_nonneg (hc _) (pow_nonneg (by have := Real.exp_pos ((Real.log (Real.log y))^2); unfold Vac.Numbers.P; positivity) _)
  have Hx : Fork (fun i => {o i}) X (fun i => {o (f i)}) U q.parent q (s.expand j) P.B Q.B (d j) e g v :=
    ⟨f, fun i _ => ⟨rfl,_,mem_singleton_self _,halo_subset _ _ (mem_image_of_mem _ (ho _)),Subset.refl _⟩,fun i => (by convert! hf' i using 2; split_ifs <;> rfl)⟩
  have hα : 0 ≤ A+1 := by unfold A; have := P.exponent_pos; linarith
  have hL : 20*(A+1)*tilePrice (s.expand j) ≤ (C.S.block m).val*Q.supportExponent := by
    apply le_trans _ (s.shape (H.shapes m)); change 20*_*tilePrice (s.expand j) ≤ 20*(Q.supportExponent + _)*_
    gcongr 20*?_*tilePrice (s.expand j)
    have ht : P.supportExponent ≤ Q.supportExponent := C.path.levels.fits.deepExp (Nat.le_succ m)
    change A+1 ≤ Q.supportExponent + s.inflate (year C (m+1)); unfold A; linarith
  have hM : Q.B ≤ 2*P.B := by have ht : Q.B^2 ≤ 2*P.B^2 := H.tabs.grows _; nlinarith
  have ht := Hx.rethread hv h.pos P.B_pos hM hα Q.exponent_pos hL (fun _ => zero_le_one) (le_refl 1) he (by simpa only [duty,prod_singleton,
    one_mul] using hB : Rooted _ X Q.B Q.supportExponent _ y⁻¹)
  let K := expense C.path.levels s d m
  have heq : A+1=(C.path.levels.params m).supportExponent+7 := by unfold A; rw [add_assoc]; norm_num; rfl
  have ht' : Rooted (fun i => {o (f i)}) U P.B (A+1) g (K*v*y⁻¹) := by simpa only [K,expense,heq,duty,div_one,
      prod_singleton,one_mul] using! ht
  have hK : 1 ≤ K := pad_ge (heq ▸ hα)
  have hA := root_hit (fibers q) h.pos (by positivity : 0 ≤ K*v*y⁻¹) (fun i _ => ⟨_,mem_singleton_self _,
    halo_subset _ _ (mem_image_of_mem _ (ho _))⟩) ht'
  intro z; apply Budget.mono (hA z)
  · intro i; split; exact mul_nonneg (h.pos _) (Real.exp_pos _).le; rfl
  · intro i; by_cases he : 0<g i ∧ z∈Y i
    · rw [if_pos he.2,if_pos (hf i he.1 he.2)]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) he.1.le
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Corona.cover_mono (hf i he.1) P.B)) (by have := (point C m).exponent_pos; linarith)
    have ht := (hA z).1 i
    rw [show (if z∈Y i then g i*Real.exp (((point C m).supportExponent+6)*coverNumber (point C m).B (Y i)) else 0) = 0 by
      split <;> rename_i hx
      · rw [le_antisymm (le_of_not_gt fun ht => he ⟨ht,hx⟩) (h.pos i), zero_mul]
      rfl]; exact ht
  have hsf : 0 ≤ siteFactor P.B := by unfold siteFactor; positivity
  calc
    _ = (siteFactor P.B * ((C.S.block m).val^4 * K)) * (v*y⁻¹) := by push_cast; change _=siteFactor P.B * (((q.count.val:ℝ))^4 * K)*(v*y⁻¹); ring
    _ ≤ (x^((1:ℝ)/4))*(y^((1:ℝ)/2)*y⁻¹) := by
      gcongr
      · exact (I.cost m).2
      exact (I.cost m).1
    _ = (x^((1:ℝ)/4))*y^(-(1:ℝ)/2) := by rw [← Real.rpow_neg_one, ← Real.rpow_add hy]; congr 2; norm_num
    _ ≤ (x^((1:ℝ)/4))*x^(-(1:ℝ)/2) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz hxy (by norm_num)) (by positivity)
    _ = x^(-(1/4:ℝ)) := by rw [← Real.rpow_add hz]; congr 1; norm_num

include H in
theorem divisor_step (hG : G.Simple) : divisor C (m+1) ≤ divisor C m := by
  let x := hat C m
  have he : (8:ℝ) ≤ Stock.scaleB x := by exact_mod_cast (H.here m).large
  have hx : 1<x := C.path.levels.fits.delayed _
  have ha := Real.log_pos hx
  have Hx := Nat.ceil_lt_add_one (sq_nonneg (Real.log x))
  have hh : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by unfold Stock.scaleB at he; nlinarith)
  have hy := nearby C m hG
  unfold divisor RG.Calendar.forcedAllowance RG.Calendar.monitor; gcongr

lemma old_root (hC : C.Makes) {s : Scope} {t : Tariff} (H : Prepared s t C.localSection C.path.levels) (hm : m≤N) (p : ℕ) :
    let P := C.path.rep N p m; let Q := point C m
    let E i := (P.activities.reg i).support; let K i := (P.activities.forced i).support
    let τ i := (P.activities.reg i).site
    ∃ (e b : ℕ→ℝ) (σ : ℕ→Site (C.side m p)),
      (∀ i, Q.supBounds (τ i) (E i) (P.activities.E i) (e i)) ∧
      (∀ i,σ i∈K i ∧ 0 ≤ b i ∧ ∀ U, ‖P.activities.K i U‖ ≤ divisor C m * b i) ∧
      Rooted (fun i => {τ i}) E Q.B Q.supportExponent e (hat C m)⁻¹ ∧
      Rooted (fun i => {σ i}) K Q.B Q.supportExponent b (hat C m)⁻¹ := by
  intro P Q E K τ
  have hp : P.p = Q := (hC.wilson.represents N p m hm).vac
  obtain ⟨e,h₁,h₂⟩ := (hC.wilson.represents N p m hm).good.labels.boundE
  obtain ⟨b,h₃,h₄⟩ := (hC.wilson.represents N p m hm).good.labels.boundK
  have hh i : (K i).Nonempty := (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
  choose σ hσ using hh
  let g := gHat C m
  have he : 0<g := gHat_pos ..
  have hg : g ≤ 1 := gHat_le_one ..
  have hx : g^2=(hat C m)⁻¹ := by
    change (Real.sqrt (hat C m))⁻¹^2 = _; rw [inv_pow,Real.sq_sqrt (zero_le_one.trans (C.path.levels.fits.delayed m).le)]
  let κ := divisor C m; have hk : 0 < κ := divisor_pos ..
  refine ⟨e,(fun i => κ⁻¹*b i),σ,hp ▸ h₁,fun i => ⟨hσ i,mul_nonneg (inv_nonneg.mpr hk.le) (h₃ i).1, ?_⟩,fun z => ?_,fun z => ?_⟩
  · rw [show divisor C m=κ from rfl,mul_inv_cancel_left₀ hk.ne']; exact (h₃ i).2
  · have he : C.path.levels.clock.allowance m ≤ (hat C m)⁻¹ := (Real.rpow_le_rpow_of_exponent_ge he hg (show (2:ℝ) ≤ 11/5 by norm_num)).trans_eq
      ((Real.rpow_two g).trans hx)
    change P.p = Q at hp
    simpa [E,τ,BudgetPoint.mass,← hp,eq_comm] using! Budget.mono (h₂ z) (h₂ z).1 (fun _ => le_rfl) he
  refine Budget.mono (Budget.scale (h₄ z) (inv_nonneg.mpr hk.le)) (fun i => ?_) (fun i => ?_) ?_
  · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (inv_nonneg.mpr hk.le) (h₃ i).1); rfl
  · rw [← hp]; simp only [Finset.mem_singleton]; split_ifs <;> rename_i hh
    · unfold BudgetPoint.mass; dsimp only [K,P]; exact le_of_eq (mul_left_comm ..)
    · rename_i h; exact (hh (h.symm ▸ hσ _)).elim
    · exact mul_nonneg (inv_nonneg.mpr hk.le) (mul_nonneg (Real.exp_pos _).le (h₃ i).1)
    rw [mul_zero]
  have hh : κ ≤ g^6 := (H.here m).vacuum
  have h : C.path.levels.clock.forcedAllowance m = κ*κ := (Real.mul_self_sqrt (Real.exp_pos _).le).symm
  rw [h,inv_mul_cancel_left₀ hk.ne',← hx]; exact hh.trans (pow_le_pow_of_le_one he.le hg (by decide))

include I H hC hc hξ in
/-- Estimates paying even an inflation on inherited K. Uniform post-L costs
and volume tests for all positive variants in these particular source-free
families, not a bound on new packet/trigger/likelihood/integration factors,
kinetic adjustments, sector sums, etc. Those need their own analysis.
The small extra halo lemma above can price `inspected` in `Variants`.
-/
theorem inherited (hG : G.Simple) (hm : m<N) (p : ℕ) :
    let Q := point C (m+1); let P := C.path.rep N p (m+1)
    let E i := (P.activities.reg i).support; let K i := (P.activities.forced i).support
    ∃ e b : ℕ→ℝ, (∀ i, Q.supBounds (P.activities.reg i).site (E i) (P.activities.E i) (e i)) ∧
      (∀ i, 0 ≤ b i ∧ ∀ U, ‖P.activities.K i U‖ ≤ divisor C m * b i) ∧
      ∀ (Y : α → Support (C.side m p)) (g : α → ℝ),
        (Variants E Y s d k c e g ∨ Variants K Y s d k c b g) →
        Ac.Hit Y (point C m).B g ((point C m).supportExponent+6) ((hat C m)^(-(1/4:ℝ))) := by
  intro Q P E K
  obtain ⟨e,b,v,hE,hb,h₁,h₂⟩ := old_root hC H hm p
  refine ⟨e,b,hE, fun i => ⟨(hb i).2.1,fun U => ((hb i).2.2 U).trans
    (mul_le_mul_of_nonneg_right (divisor_step H hG) (hb i).2.1)⟩,fun Y g h => ?_⟩
  rcases h with h|h
  · exact h.cashed H I hc hξ hG (fun i => (hE i).1) _ (fun i => (P.activities.reg i).anchor) h₁
  exact h.cashed H I hc hξ hG (fun i => (hb i).2.1) v (fun i => (hb i).1) h₂

end Prices
end YM.Extra.Multi.System

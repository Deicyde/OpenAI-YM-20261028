import YM.Next.WARD_BIN.Vectors
import YM.Work.G06.Average
import YM.Work.G07
import YM.Work.G08


/-!
# The common cutoff test, before aggregating the forced parts

Prices of probe bodies in *dimensionless* units. No period costs hidden
in the families of stencils with these provisions. Weight parameters fixed
by the call. No cone or direction assumed. Propagate later with `Direction`
only AFTER subtraction; prices here feed the purchases at cutoff for the
signed density. Constants are visible (producers will use `Exists`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G07 Bid
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {H : Hol G} {m d k P : ℕ} {F : Labels.Frame G d} {n : Side}

lemma liftBound {o : Directions G n → Prop} {h : Config G n→Prop} {u : Config G n → ℂ}
    {c t : ℝ} (hx : LeftBound k o h 1 c u) (hv : c ≤ t) : LeftBound k o h 1 t u :=
  ⟨hx.smooth,hx.nonneg.trans hv,fun l hl he U hu => (hx.bound l hl he U hu).trans (by simp only [one_pow, mul_one]; exact hv)⟩

lemma complexBound {D : Directions G n → Prop} {Z : Config G n → Prop}
    {f : Config G n → ℂ} {c : ℝ} (h : LeftBound k D Z 1 c f) (t : ℂ) : LeftBound k D Z 1 (‖t‖*c) fun U => t*f U := by
  let L := ((ContinuousLinearMap.mul ℂ ℂ t).restrictScalars ℝ)
  refine ⟨h.smooth.postcomp L,mul_nonneg (norm_nonneg _) h.nonneg,fun l hl hv U hs => ?_⟩
  change ‖leftDerivs (fun U => L (f U)) l U‖ ≤ _
  rw [left_linear h.smooth L hl]; change ‖t*leftDerivs f l U‖ ≤ _; rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.bound l hl hv U hs) (norm_nonneg _)

lemma coeff_add (x y : F.Coeff) : F.coeffSize (x+y) ≤ F.coeffSize x + F.coeffSize y := by
  unfold Labels.Frame.coeffSize; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => norm_add_le _ _
lemma coeff_le (x : F.Coeff) : ‖x‖ ≤ F.coeffSize x := by
  refine (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg F x)).2 fun i => ?_
  exact Finset.single_le_sum (f:=fun i => ‖x i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ _)

lemma coeff_smul (x : F.Coeff) (t : ℂ) : F.coeffSize (t • x) = ‖t‖ * F.coeffSize x := by
  simp only [Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,Finset.mul_sum]

/-- Test `f,q` (body, unscaled projection), in dimensionless units at anchor.
Uniform body price c with `t⁻ᵈ` allowance on full group. Derivative order k
here used at the designated call (`k=b.order` later). -/
structure Coin (H : Hol G) (F : Labels.Frame G d) (S : Finset Cover) (k : ℕ) (b : BudgetPoint)
    (o : Site n) (f : CoverConfig G → ℂ) (q : Label G d) (c : ℝ) : Prop where
  localizes : LocalOn S f
  smooth : Continuous f
  invariant : GaugeInvariant f
  reads : Projects H q f
  body : LeftBound k (b.dirBound o) (Healthy b.threshold (footprint S o)) 1 c (places o f)
  weights : F.coeffSize (F.scaled b.threshold (F.coords q)) ≤ c
  group U : ‖f U‖ ≤ c*b.threshold⁻¹^d

namespace Coin
variable {k : ℕ} {c c' : ℝ} {S : Finset Cover} {b : BudgetPoint} {o : Site n}
    {x y : CoverConfig G → ℂ} {p q : Label G d}

lemma raise (h : Coin H F S k b o x p c) (hx : c ≤ c') : Coin H F S k b o x p c' :=
  { h with body := liftBound h.body hx
           weights := h.weights.trans hx
           group U := (h.group U).trans <| mul_le_mul_of_nonneg_right hx (pow_nonneg (inv_pos.mpr b.threshold_pos).le _) }

lemma add (h : Coin H F S k b o x p c) (ht : Coin H F S k b o y q c') : Coin H F S k b o (x+y) (p+q) (c+c') := by
  refine ⟨fun U V he => congr_arg₂ (· + ·) (h.localizes U V he) (ht.localizes U V he), h.smooth.add ht.smooth,
    fun t U => congr_arg₂ (· + ·) (h.invariant t U) (ht.invariant t U), ?_, h.body.add ht.body,?_,?_⟩
  · intro A
    obtain ⟨a,b,he⟩ := h.reads A
    obtain ⟨g,p,hq⟩ := ht.reads A
    dsimp only; simp only [Pi.add_apply,Submodule.coe_add,map_add]
    refine ⟨a.add g,b.add p,fun j hj => ?_⟩
    have hi : (↑j:WithTop ℕ∞)≤(d:ℕ∞) := by exact_mod_cast hj
    rw [iteratedDeriv_fun_add (a.of_le hi) (g.of_le hi),iteratedDeriv_fun_add (b.of_le hi) (p.of_le hi),he j hj,hq j hj]
  · rw [map_add,map_add]; exact (coeff_add ..).trans (add_le_add h.weights ht.weights)
  intro U; rw [add_mul]
  exact (norm_add_le (x U) (y U)).trans (add_le_add (h.group _) (ht.group _))

lemma smul (h : Coin H F S k b o x p c) (t : ℂ) : Coin H F S k b o (t • x) (t • p) (‖t‖*c) := by
  refine ⟨fun U V e => congr_arg (t • ·) (h.localizes U V e), h.smooth.const_smul _,
    fun _ U => congr_arg (t • ·) (h.invariant _ U), Work.G06.projects_smul h.reads _,complexBound h.body _,?_,?_⟩
  · rw [map_smul,map_smul, coeff_smul]; exact mul_le_mul_of_nonneg_left h.weights (norm_nonneg _)
  intro U; rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h.group _) (norm_nonneg _)

lemma sub (h : Coin H F S k b o x p c) (ht : Coin H F S k b o y q c') : Coin H F S k b o (x-y) (p-q) (c+c') := by
  have he := h.add (ht.smul (-1)); rw [norm_neg,norm_one,one_mul, neg_smul,one_smul, show (-1 : ℂ) • q = -q from neg_one_smul ℂ q, ← sub_eq_add_neg, ← sub_eq_add_neg] at he; exact he

lemma zero : Coin H F S k b o 0 0 0 := by
  refine ⟨fun U V he => rfl,continuous_const, fun t U => rfl, ?_, ?_, ?_, by simp⟩
  · intro A; simp; exact contDiffAt_const
  · simpa only [norm_zero] using! (LeftBound.const (G:=G) (D:=b.dirBound o) (k:=k)
      (Z:=Healthy b.threshold (footprint S o)) zero_le_one (0:ℂ))
  simp [Labels.Frame.coeffSize]

lemma sum {J : Type*} (I : Finset J) (u : J → Label G d) (f : J → CoverConfig G → ℂ) (q : J→ℝ)
    (h : ∀ i∈I,Coin H F S k b o (f i) (u i) (q i)) : Coin H F S k b o
      (∑ i∈I,f i) (∑ i∈I,u i) (∑ i∈I,q i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero
  | insert i I hx ih =>
    simp only [Finset.sum_insert hx]; exact (h i (Finset.mem_insert_self ..)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- Pay l1 over this finite presentation, don't extrapolate to all
stencils at a scale. -/
lemma gross {J : Type*} [Fintype J] (v : J→ℂ) (u : J → Label G d) (f : J → CoverConfig G → ℂ) (q : J→ℝ)
    (h : ∀ i,Coin H F S k b o (f i) (u i) (q i)) : Coin H F S k b o
      (∑ i,v i • f i) (∑ i,v i • u i) ((∑ i,q i)*‖v‖) := by
  refine (sum _ _ _ (fun i : J => ‖v i‖*q i) (fun i _ => (h i).smul (v i))).raise ?_
  rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (h i).body.nonneg

/-- Useful when presenting a generator with an additional power of t in the
coefficient, not applied to the actual coupling after absorbing it. Pay up to
t^{-d} global. The superscripts in labels are preserved exactly. -/
lemma generator {l : ℕ} (hl : l ≤ d) (m : ℕ) (u : CoverConfig G → ℂ) (q : Label G d)
    (p : GaugeInvariant u) (hq : Projects H q u) (hf : Affordable S ((l:ℤ)-m) u)
    (hm : ∀ i j,i≤d → j≤d → j+m < l → gradePart (i,j) q=0) (k P : ℕ) (F : Labels.Frame G d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Side, FitsIn S n → ∀ b : BudgetPoint, b.power=P → ∀ o : Site n,
    let t := b.threshold
    Coin H F S k b o (((t:ℂ)^m / (t:ℂ)^l) • u) (((t:ℂ)^m / (t:ℂ)^l) • q) C := by
  obtain ⟨c,hc,hC⟩ := hf.paid k P
  obtain ⟨g,hg⟩ := hf.cont.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  have gh : 0 ≤ g := le_trans (norm_nonneg (u 1)) (hg _)
  let K := F.coeffSize (F.coords q)
  have hK : 0 ≤ K := Work.G08.size_nonneg _ _
  refine ⟨c+g+K,add_nonneg (add_nonneg hc gh) hK,fun n hn b hb o => ?_⟩
  let t := b.threshold
  have hu : 0<t := b.threshold_pos
  let z : ℂ := (t:ℂ)^m / (t:ℂ)^l
  have hz : ‖z‖ = t^m/t^l := by simp [z,norm_pow,abs_of_pos hu]
  refine ⟨fun U V he => congr_arg (fun w : ℂ => z • w) (hf.uses U V he),hf.cont.const_smul z,
    fun T U => congr_arg (fun w : ℂ => z • w) (p T U), Work.G06.projects_smul hq z,?_,?_,?_⟩
  · have hW := complexBound (hC n hn b hb o) z
    refine liftBound hW (le_trans (le_of_eq ?_) (show c≤c+g+K by linarith))
    rw [hz, zpow_sub₀ (b.threshold_pos.ne'), zpow_natCast, zpow_natCast]; unfold t
    field_simp [b.threshold_pos.ne']
  · refine le_trans ?_ (show K ≤ c+g+K by linarith)
    have hw {i : F.Index} (h : (F.grades i).2 + m < l) : F.coords q i=0 := by
      rw [← decompose q, map_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero; intro x hx
      rw [map_sum, Finset.sum_apply]; apply Finset.sum_eq_zero; intro y hy
      by_cases hb : (x,y)=F.grades i
      · have he : y=(F.grades i).2 := congr_arg Prod.snd hb
        rw [hm x y (Nat.le_of_lt_succ (Finset.mem_range.mp hx))
          (Nat.le_of_lt_succ (Finset.mem_range.mp hy)) (by rwa [he]),map_zero]; rfl
      exact F.power_coefficient i hb (gradePart_mem ..)
    change F.coeffSize (F.scaled t (F.coords (z • q))) ≤ F.coeffSize (F.coords q)
    rw [map_smul]; apply Finset.sum_le_sum; intro i _
    rcases lt_or_ge ((F.grades i).2+m) l with h|h
    · simp [hw h]
    rw [F.scaled_apply,norm_mul, Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hu.le _), hz, ← mul_assoc]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [← mul_div_assoc,← pow_add, div_le_one (pow_pos hu _)]; exact pow_le_pow_of_le_one hu.le b.threshold_le h
  intro U
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (show g≤c+g+K by linarith) (pow_nonneg (inv_pos.mpr b.threshold_pos).le _))
  change ‖z • u U‖ ≤ _; rw [norm_smul, hz,mul_comm _ (t⁻¹^d)]
  refine mul_le_mul ?_ (hg U) (norm_nonneg _) (by positivity)
  rw [div_eq_mul_inv, ← inv_pow]
  exact le_trans (mul_le_of_le_one_left (by positivity) (pow_le_one₀ hu.le b.threshold_le))
    (pow_le_pow_right₀ ((one_le_inv₀ hu).mpr b.threshold_le) hl)
end Coin

variable {S : Finset Cover} {b : BudgetPoint}

lemma row_price (R : Rays G d H) (h : R.FitsAt S) (B : PureBasis G d) (i : Count G d) (F : Labels.Frame G d)
    (k P : ℕ) :
    ∃ c : ℝ,0≤c ∧ ∀ b : BudgetPoint, b.power=P → ∀ n,FitsIn S n → ∀ o : Site n, ∀ β : ℝ, 0<β →
      β⁻¹/b.threshold^ (2:ℕ) ≤ 2 →
      Coin H F S k b o (B.row R β b.threshold i) (B.xRow R h β b.threshold i) c := by
  let l := B.s i+1
  have hl : l≤d := B.le i
  let p := R.force (B.form i)
  let q := R.compression (B.form i)
  let P₁ := readout d H (B.fPaid R h i) (B.fInv R i)
  let P₂ := readout d H (B.dPaid R h i) (B.dInv R h i)
  have hr (f : CoverConfig G → ℂ) (m : ℕ) (v : GaugeInvariant f) (r : Affordable S ((l:ℤ)-m) f) :
      ∀ i j : ℕ,i≤d → j≤d → j+m < l → gradePart (i,j) (readout d H r v) = 0 := by
    intro i j hi hj he
    rw [grade_readout H r v hj hi]; exact crownAt_below r H v (by omega)
  obtain ⟨c,hc,hp⟩ := Coin.generator hl 0 p P₁ (B.fInv R i)
    (reading H (B.fPaid R h i) _ d) (B.fPaid R h i) (hr p 0 _ _) k P F
  obtain ⟨e,he,hq⟩ := Coin.generator hl 2 q P₂ (B.dInv R h i)
    (reading H (B.dPaid R h i) _ d) (B.dPaid R h i) (hr q 2 _ _) k P F
  refine ⟨c+2*e,by positivity,fun b hb n hn o β ht hg => ?_⟩
  let t := b.threshold
  let T : ℂ := (t:ℝ)
  let Z : ℂ := (β:ℝ)
  have hv := hp _ hn _ hb o
  have he' := (hq n hn b hb o).smul (Z⁻¹/T^2)
  have hE : Z⁻¹/T^2 * (T^ (2:ℕ)/T^l) = (T^l)⁻¹ * Z⁻¹ := by
    have hz : T ≠ 0 := Complex.ofReal_ne_zero.mpr b.threshold_pos.ne'
    field_simp
  have hu : ‖Z⁻¹/T^ (2:ℕ)‖ ≤ 2 := by
    simp only [T, Z,norm_div,norm_inv,norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (show 0≤t from b.threshold_pos.le)]; exact hg
  have hp := (hv.sub he').raise (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hu he))
  simp only [pow_zero,one_div,smul_smul] at hp
  change Coin _ _ _ _ _ _ ((T^l)⁻¹ • p - (Z⁻¹/T^2*(T^2/T^l)) • q) ((T^l)⁻¹ • P₁-(Z⁻¹/T^2*(T^2/T^l)) • P₂) _ at hp
  rw [hE, ← smul_smul, ← smul_smul, ← smul_sub,← smul_sub (T^l)⁻¹ P₁ (Z⁻¹ • P₂)] at hp
  exact hp

lemma eq_price (B : PureBasis G d) (R : Rays G d H) (h : R.FitsAt S) (F : Labels.Frame G d)
    (k P : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ b : BudgetPoint,b.power=P → ∀ n,FitsIn S n → ∀ o : Site n, ∀ β : ℝ, 0<β →
      β⁻¹/b.threshold^ (2:ℕ) ≤ 2 → ∀ v : PureBasis.Grid G d,
      Coin H F S k b o (B.tree R β b.threshold v) (B.xTree R h β b.threshold v) (c*‖v‖) := by
  classical
  choose c hc hh using fun i => row_price R h B i F k P
  exact ⟨∑ i,c i, Finset.sum_nonneg (fun i _ => hc i), fun b hb n he o β ht hp v =>
    Coin.gross v _ _ _ fun i => hh i _ hb n he o β ht hp⟩

-- Use canonical pop receipt with k,P explicitly chosen.
def canonical (Q : SectionData F) (t : ℝ) (x : F.Coeff) := Q.evaluate (F.scaled t⁻¹ x)
def primary (F : Labels.Frame G d) (t : ℝ) (x : F.Coeff) := F.coords.symm (F.scaled t⁻¹ x)

lemma basis_degree (i : F.Index) : (F.grades i).2 ≤ d := by
  classical
  let v := F.basis i
  have h : v.val ≠ 0 := fun e => (Module.Basis.ne_zero F.basis i) (Subtype.ext e)
  obtain ⟨l,hL⟩ := (Finset.nonempty_iff_ne_empty.mpr (fun H => h (MvPolynomial.support_eq_empty.mp H)) : v.val.support.Nonempty)
  have hi := (pure_grade _ v).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hL)
  have hv := weight_slot (G:=G) l
  have hp := power_le l
  rw [hi] at hp; rw [hi] at hv
  exact hp.trans ((congrArg Prod.fst hv).symm.trans_le (F.bound i))

private lemma vector_cost (Q : SectionData F) (h : Q.Sound H) (hp : pop Q) (ht : Q.stencil ⊆ S)
    (i : F.Index) (k P : ℕ) :
    ∃ c : ℝ, 0≤c ∧ ∀ n,FitsIn S n → ∀ b : BudgetPoint, b.power=P → ∀ o : Site n,
      Coin H F S k b o (canonical Q b.threshold (Pi.single i 1)) (primary F b.threshold (Pi.single i 1)) c := by
  let x : F.Coeff := Pi.single i 1
  obtain ⟨m,B,hB,p,hP,hR⟩ := hp i
  let l := (F.grades i).2
  have he : Affordable Q.stencil (l:ℤ) (Q.evaluate x) :=
    Affordable.fromRate (Q.cylinder_local x) (fun _ _ => hP.symm ▸ paid_lumin p B hB hR)
  have hf : Affordable S ((l:ℤ)-(↑(0:ℕ):ℤ)) (Q.evaluate x) := by simpa using he.widen ht
  have hu : F.coords.symm x = F.basis i := F.coords.injective (by rw [F.coords_basis,LinearEquiv.apply_symm_apply])
  have hb : ∀ b j : ℕ,b≤d → j≤d → j+0 < l → gradePart (b,j) (F.coords.symm x) = 0 := by
    intro b j _ _ hj; rw [hu]; apply gradePart_zero _ _ _ _ (F.pure i)
    intro h; have he : j=l := congr_arg Prod.snd h; omega
  obtain ⟨c,hc,H⟩ := Coin.generator (basis_degree i) 0 (Q.evaluate x) (F.coords.symm x) (h.gaugeInvariant x)
    (h.projects x) hf hb k P F
  refine ⟨c,hc,fun n hn b hb o => ?_⟩
  have hv : F.scaled b.threshold⁻¹ (Pi.single i 1) = _ := calc
    _ = ((↑b.threshold:ℂ)^l)⁻¹ • F.coords (F.basis i) := by
      rw [← F.coords_basis i,F.scaled_pure _ _ (F.pure i), inv_pow,
        Complex.ofReal_inv, Complex.ofReal_pow]
    _ = ((↑b.threshold:ℂ)^l)⁻¹ • x := by rw [F.coords_basis i]
  unfold canonical primary; rw [hv, Q.eval_linear.map_smul,map_smul]
  simpa only [pow_zero,one_div] using! H n hn b hb o


lemma primary_price (Q : SectionData F) (h : Q.Sound H) (hp : pop Q) (ht : Q.stencil ⊆ S)
    (k P : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ n,FitsIn S n → ∀ b : BudgetPoint, b.power=P → ∀ o : Site n, ∀ x : F.Coeff,
      Coin H F S k b o (canonical Q b.threshold x) (primary F b.threshold x) (c*‖x‖) := by
  classical
  choose c hc hh using fun i => vector_cost Q h hp ht i k P
  let A := ∑ i:F.Index,c i
  refine ⟨max 1 A,le_max_left _ _, fun n hn b hb o x => ?_⟩
  let g := fun i : F.Index => (Pi.single i (1:ℂ) : F.Coeff)
  have Hx : ∑ i, x i • g i = x := calc
    _ = F.coords (∑ i,x i • F.basis i) := by rw [map_sum]; simp_rw [map_smul,F.coords_basis];rfl
    _ = x := by
      have hx : ∑ i : F.Index, x i • F.basis i = F.coords.symm x := by
        conv_lhs => rw [show x = F.coords (F.coords.symm x) from (F.coords.apply_symm_apply _).symm]
        exact F.basis.sum_repr _
      rw [hx,F.coords.apply_symm_apply]
  have h (p : ℝ) : IsLinearMap ℂ (canonical Q p) := by
    unfold canonical; constructor <;> intro x y
    · rw [map_add,Q.eval_linear.map_add]
    rw [map_smul,Q.eval_linear.map_smul]
  let M := IsLinearMap.mk' (canonical Q b.threshold) (h b.threshold)
  let V := F.coords.symm.toLinearMap.comp (F.scaled b.threshold⁻¹)
  change Coin _ _ _ _ _ _ (M x) (V x) (max 1 A * _)
  have hv := Coin.gross x _ _ c (fun i => show Coin H F S k b o (M (g i)) (V (g i)) (c i) from hh i n hn b hb o)
  simp_rw [← map_smul,← map_sum,Hx] at hv; exact hv.raise (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
/-! Layout faithfulness check. Keep both global and torus tests; a pinned
nonzero read is enough to certify a nonzero torus observable. -/




end YM.WardBin

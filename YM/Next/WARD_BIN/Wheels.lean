import YM.Next.WARD_BIN.Lies
import YM.Work.F03.Flat
import YM.Work.H03




/-!
# Rotated and copied actual Regular budgets

`sendEdge` pays negative direction at the far endpoint. Even infinitesimal
order inside one edge reverses: prove one parameter permutation for *each*
splitting term all at once, using conjugation by fixed base U. Symmetrize
partials of the path, **not ordered group derivatives**. Cost Stage-local.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Wheels
open Function Finset Lattice Wilson RG Filter Topology Lies
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : BudgetPoint} {S : Support n} (s : Signed) (b : Site n) (U : Config G n) {V : Config G n} {o : Site n}

def aerial : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)





/-- Incidence and supports. -/
lemma sampling {t : ℝ} : S.image (affine s b) ∩ flags t U=(S ∩ flags t (pull s b U)).image (affine s b) := by
  rw [image_inter _ _ (show Injective (affine s b) from (aerial s b).injective), Work.H03.flags_send]
lemma safe {t : ℝ} : Healthy t (S.image (affine s b)) U ↔ Healthy t S (pull s b U) := by
  unfold Healthy
  conv_lhs => rw [← Work.H03.flags_send s b]
  exact disjoint_image (aerial s b).injective
lemma same_roof (hf : Agrees ↑(S.image (affine s b)) U V) : Agrees (S:Set _) (pull s b U) (pull s b V) := by
  rintro ⟨x,i⟩ hx ht
  have hz : (affine s b x) ∈ S.image (affine s b) := mem_image_of_mem _ (by exact hx)
  have he : (affine s b x + ((posDir i).rotate s).vec) ∈ S.image (affine s b) := by
    rw [Step.vec_rotate,Step.vec_pos,show affine s b x + s.act (step i)=affine s b (x+step i) by
      unfold affine; rw [Signed.act_add]; abel]
    exact mem_image_of_mem _ ht
  let q := [ ((posDir i).rotate s) ]
  have hG (U : Config G n) : pull s b U (x,i)=travel U (affine s b x) q := by simp [pull,q,travel]
  rw [hG,hG]; apply travel_local (affine s b x) q
  refine agrees_mono hf ?_; intro y hy; simp only [Set.mem_setOf_eq,q,visits,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl; exact hz; exact he

lemma trans_local {f : Config G n → F} (hf : LocalOn (S:Set _) f) : LocalOn ↑(S.image (affine s b)) (f ∘ pull s b) := fun U V h => hf (pull s b U) (pull s b V) (same_roof s b U h)
lemma trans_gauge {f : Config G n → F} (hf : GaugeInvariant f) : GaugeInvariant (f ∘ pull s b) := by
  intro k U
  simp only [comp_apply]
  rw [show pull s b (gauge k U)=gauge (k ∘ affine s b) (pull s b U) from ?_]; exact hf _ _
  funext e; simp only [pull,Lattice.gauge,Function.comp_apply]
  rw [Step.gauge_read,Step.vec_rotate,Step.vec_pos, show affine s b (e.1+step e.2)=affine s b e.1+s.act (step e.2) by simp only [affine,Signed.act_add]; abel]

lemma pull_by (i : Edge (Site n)) : pull s b U i= if s.flip i.2 then (U (sendEdge s b i))⁻¹ else U (sendEdge s b i) := by
  simp only [sendEdge,pull,Step.read,Step.rotate,posDir,Bool.false_xor]
variable {l : ℕ} {f : Config G n→ E} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
lemma germs (hf : Germ l f (pull s b U)) : Germ l (f ∘ pull s b) U := by
  refine hf.curves (x:=(0:Directions G n)) (Z:=fun t => pull s b (increment U t)) (by rw [Work.G07.at_zero_increment]) fun i => ?_
  simp_rw [pull_by]; cases h : s.flip i.2
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact grins (A:=id) (fun _ => contDiffAt_const) contDiffAt_id _
  simp only [↓reduceIte,G.mat_inv]
  exact (starL' ℝ (A:=G.Mat)).contDiff.contDiffAt.comp _ (grins (U:=fun _ => U) (l:=l) (x:=0) (A:=id) (fun _ => contDiffAt_const) contDiffAt_id _)

/-
For sign-pure directions use an honest permutation. Avoid product mathlib
order conventions by recursion. `dag` conjugates inversions by U *fixed*,
rather than the base of an increment when consuming remaining directions.
-/
def punct {R : Type*} [Monoid R] (l : ℕ) (f : Fin l → R) : R :=
  match l with
  | 0 => 1
  | k+1 => punct k (Fin.tail f)*f 0
lemma punct_cons {R : Type*} [Monoid R] (l : ℕ) (f : Fin l → R) (v : R) : punct _ (Fin.cons v f)=punct l f * v := by simp [punct]
lemma punct_snoc {R : Type*} [Monoid R] (l : ℕ) (f : Fin l → R) (v : R) : punct _ (Fin.snoc f v)=v*punct l f := by
  induction l with
  | zero =>
    rw [punct,punct]; change 1*Fin.snoc (α:=fun _=>R) f v (Fin.last 0)=v*1; rw [Fin.snoc_last,mul_one,one_mul]
  | succ j ih =>
    conv_lhs => rw [← Fin.cons_self_tail f, ← Fin.cons_snoc_eq_snoc_cons]
    rw [punct_cons,ih,mul_assoc,punct]

lemma journey_value (A : Slab G n l) (t : Panels l) (e) : journey U l A t e=
    punct l (fun i => G.lieExp (t i • A i e))*U e := by
  induction l generalizing U with
  | zero => simp only [punct,one_mul]; rfl
  | succ k ih =>
    rw [show journey U _ A t=journey (increment U (t 0 • A 0)) _ (Fin.tail A) (Fin.tail t) from rfl,ih,punct,mul_assoc]; rfl

abbrev sending : Equiv.Perm (Edge (Site n)) := Equiv.ofBijective (sendEdge s b) ⟨sendEdge_injective s b,
  Finite.injective_iff_surjective.mp (sendEdge_injective s b)⟩
def Purity (a : Directions G n) (r : Bool) := ∀ e,s.flip e.2≠r → a (sendEdge s b e)=0
def picked (a : Directions G n) (r : Bool) : Directions G n := fun i => if s.flip ((sending s b).symm i).2=r then a i else 0
lemma picked_pure (a : Directions G n) (r : Bool) : Purity s b (picked s b a r) r := by
  intro i hi
  rw [show sendEdge s b i=(sending s b) i from rfl]; simp only [picked,Equiv.symm_apply_apply,if_neg hi]
lemma picked_all (a : Directions G n) : a=∑ i : Bool,picked s b a i := by
  rw [Fintype.sum_bool]; funext e; simp only [Pi.add_apply,picked]; cases s.flip _ <;> simp
def dag (a : Directions G n) : Directions G n := fun i => if s.flip i.2 then G.adjoint ((U (sendEdge s b i))⁻¹) (-a (sendEdge s b i)) else a (sendEdge s b i)

open Equiv in
lemma ride (A : Slab G n l) (r : Fin l → Bool) (hr : ∀ i,Purity s b (A i) (r i)) : ∃ J : Perm (Fin l),∀ t : Panels l,∀ e : Edge (Site n),
    let v (i) := G.lieExp (t i • dag s b U (A i) e)
    let a := sendEdge s b e
    let w (i) := G.lieExp (t i • A i a)
    punct l (v ∘ J) = if s.flip e.2 then (U a)⁻¹ * (punct l w)⁻¹ * U a else punct l w := by
  let V (A : Directions G n) (t : ℝ) (e : Edge (Site n)) := G.lieExp (t • dag s b U A e)
  let W (A : Directions G n) (t : ℝ) (e : Edge (Site n)) := G.lieExp (t • A (sendEdge s b e))
  induction l with
  | zero =>
    refine ⟨Equiv.refl _,fun t e => ?_⟩
    dsimp only; cases s.flip e.2 <;> simp [punct]
  | succ l ih =>
    obtain ⟨P,hP⟩ := ih (Fin.tail A) (Fin.tail r) fun i => hr i.succ
    let J := Perm.decomposeFin.symm (0,P)
    have he (Q : Fin (l+1) → G.El) : Q ∘ J = Fin.cons (Q 0) (Fin.tail Q ∘ P) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [J,Fin.tail]
    have hh (t : Panels (l+1)) (e : Edge (Site n)) :
        let v (i) := G.lieExp (t i • dag s b U (A i) e)
        let w (i) := W (A i) (t i) e
        let a := sendEdge s b e
        punct _ (Fin.tail v ∘ P) = if s.flip e.2 then (U a)⁻¹ * (punct _ (Fin.tail w))⁻¹ * U a else punct _ (Fin.tail w) := hP (Fin.tail t) e
    rcases hA : r 0 with _|_
    · refine ⟨J,fun t e => ?_⟩; dsimp only
      rw [he,punct_cons]
      change _ = if _ then _ * (punct _ (fun i => W (A i) (t i) e))⁻¹ * _ else punct _ (fun i => W (A i) (t i) e)
      rw [hh,punct]
      cases hz : s.flip e.2 with
      | true =>
        have hE := hr 0 e (by simp [hA,hz]); simp only [W, ↓reduceIte,dag,hE,smul_zero,neg_zero,map_zero,hz,G.mat_lieExp_zero,mul_one]
      | false => simp only [W,Bool.false_eq_true,↓reduceIte,dag,hz]
    refine ⟨(finRotate _).trans J,fun t e => ?_⟩; dsimp only
    let Q (i) := G.lieExp (t i • dag s b U (A i) e)
    change punct _ ((Q ∘ J) ∘ finRotate _) = if _ then _ * (punct _ (fun i => W (A i) (t i) e))⁻¹ * _ else punct _ (fun i => W (A i) (t i) e)
    rw [he, show Fin.cons (Q 0) (Fin.tail Q ∘ P) ∘ finRotate _=Fin.snoc (α:=fun _ => G.El) (Fin.tail Q ∘ P) (Q 0) from (Fin.snoc_eq_cons_rotate ..).symm, punct_snoc]
    unfold Q; rw [hh,punct]; cases hz : s.flip e.2
    · have hE := hr 0 e (by simp [hA,hz]); simp only [W,Bool.false_eq_true, ↓reduceIte,hE,smul_zero,dag,hz,G.mat_lieExp_zero,mul_one,one_mul]
    simp only [↓reduceIte,mul_inv_rev,hz,W,dag]
    rw [← map_smul,← expAdjoint,smul_neg,Work.F03.exp_neg_color, inv_inv]; group

lemma rides (A : Slab G n l) (r : Fin l → Bool) (hr : ∀ i,Purity s b (A i) (r i)) : ∃ J : Equiv.Perm (Fin l),∀ t : Panels l,
    pull s b (journey U l A t)= journey (pull s b U) l ((dag s b U ∘ A) ∘ J) (t ∘ J) := by
  obtain ⟨J,hJ⟩ := ride s b U A r hr
  refine ⟨J,fun t => ?_⟩
  funext e
  rw [journey_value]
  rw [show (fun i => G.lieExp ((t ∘ J) i • ((dag s b U ∘ A) ∘ J) i e))=(fun i => G.lieExp (t i • dag s b U (A i) e)) ∘ J from rfl]
  rw [hJ, pull_by,pull_by, journey_value]
  cases s.flip e.2
  · simp
  simp only [↓reduceIte]; group

lemma picked_bounded {a : Directions G n} (ha : p.dirBound (affine s b o) a) (r : Bool) : p.dirBound (affine s b o) (picked s b a r) := by
  intro i; rw [picked]; split; exact ha i
  rw [norm_zero]; exact mul_nonneg p.threshold_pos.le (by positivity)
lemma dag_bounded {a : Directions G n} (ha : p.dirBound (affine s b o) a) : p.dirBound o (((2 : ℝ)^p.power)⁻¹ • dag s b U a) := by
  intro i
  let q := sendEdge s b i
  have hp : separation q.1 (affine s b i.1) ≤ 1 := by
    unfold q sendEdge Step.used; split
    · unfold separation
      simp only
      rw [sub_right_comm,sub_self,zero_sub,pdist_neg]; exact pdist_step _
    simp
  have hq : separation q.1 (affine s b o) ≤ separation i.1 o+1 :=
    (separation_triangle q.1 (affine s b i.1) _).trans (add_comm _ (separation i.1 o) ▸
      add_le_add hp (by simp [affine]))
  have he : ‖dag s b U a i‖=‖a q‖ := by unfold dag; split; rw [G.norm_adjoint, norm_neg]; exact rfl
  rw [Pi.smul_apply,norm_smul,he,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (ha q) (by positivity)).trans
  rw [inv_mul_le_iff₀ (by positivity)]
  conv_rhs => rw [mul_left_comm, ← mul_assoc p.threshold] -- need get threshold upfront
  rw [mul_assoc p.threshold,← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) p.threshold_pos.le
  have hh : (↑(separation q.1 (affine s b o)):ℝ) ≤ (separation i.1 o:ℝ)+1 := by exact_mod_cast hq
  linarith [Nat.cast_nonneg (α:=ℝ) (separation i.1 o)]

-- Enlargement and scalar price common to every site in derivative lists
lemma rotated_mixed (A : Slab G n l) (r : Fin l → Bool) (hr : ∀ i,Purity s b (A i) (r i)) (hf : Germ l f (pull s b U)) : ∃ J : Equiv.Perm (Fin l),
    mixed (f ∘ pull s b) l U A=mixed f l (pull s b U) (dag s b U ∘ A ∘ J) := by
  obtain ⟨J,hJ⟩ := rides s b U A r hr
  let D := dag s b U ∘ A ∘ J
  let g := f ∘ journey (pull s b U) _ D
  let M : Panels l →L[ℝ] Panels l := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (J i)
  have hE (i : Fin l) : M (cart i)=cart (J.symm i) := by
    funext j; change cart i (J j)= _; by_cases h : J j=i
    · rw [← h]; simp
    simp [cart,h, show j≠J.symm i from fun H => h (by rw [H,J.apply_symm_apply])]
  have he : (f ∘ pull s b) ∘ journey U l A=g ∘ M := funext fun t => congr_arg f (hJ t)
  have hG : ContDiffAt ℝ l g 0 := hf.journeys D
  have hx := germs s b U hf
  refine ⟨J,?_⟩
  change _=mixed f l _ D
  rw [← hf.takes D (le_refl _),← hx.takes A (le_refl _),hf.ordered D,hx.ordered A,he,liner M (by rw [M.map_zero]; exact hG)]
  simp_rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,hE,map_zero]
  exact YM.Analysis.sym_Jet hG cart J.symm

lemma pure_payment {m c} (hp : m≤p.order) (hf : Germ p.order f (pull s b U)) (h : Healthy p.threshold S (pull s b U)) (hh : p.supBounds o S f c) (A : Slab G n m) (r : Fin m→Bool) (ht : ∀ i,Purity s b (A i) (r i)) (ha : ∀ i,p.dirBound (affine s b o) (A i)) :
    ‖mixed (f ∘ pull s b) m U A‖ ≤ ((2:ℝ)^p.power)^m * c := by
  obtain ⟨J,hJ⟩ := rotated_mixed s b U A r ht (hf.prod hp)
  let k := ((2:ℝ)^p.power)
  have hk : 0<k := by unfold k; positivity
  let v (i) : Directions G n := k⁻¹ • dag s b U (A (J i))
  rw [hJ,show dag s b U ∘ A ∘ J = fun i => k • v i from funext fun i => (smul_inv_smul₀ hk.ne' _).symm]
  rw [(mixed f m _).map_smul_univ (fun _=>k) v,prod_const,card_univ,Fintype.card_fin,norm_smul,Real.norm_of_nonneg (by positivity),← hf.takes v hp]
  refine mul_le_mul_of_nonneg_left (hh.2 _ h _ (by simpa using hp) ?_) (by positivity)
  intro B hb; obtain ⟨i,hh⟩ := List.mem_ofFn.mp hb; exact hh ▸ dag_bounded s b U (ha (J i))


def tariff (p : BudgetPoint) := ((2:ℝ)^p.order)* (((2:ℝ)^p.power)^p.order)
lemma tariff_positive (p : BudgetPoint) : 0<tariff p := by unfold tariff; positivity
lemma regular_carry [MeasurableSpace E] (hf : p.Regular S f) : p.Regular (S.image (affine s b)) (f ∘ pull s b) := by
  have he U (h : Healthy p.threshold (S.image (affine s b)) U) := germs s b U (show Germ p.order f (pull s b U) from hf.smooth _ ((safe s b U).mp h))
  exact ⟨trans_local s b hf.sites,hf.borel.comp (continuous_pull ..).measurable,trans_gauge s b hf.symmetry,he,fun U h A x l => (he U h).has x A l⟩
lemma carry_bound {c} [MeasurableSpace E] (hf : p.Regular S f) (hg : p.supBounds o S f c) :
    p.supBounds (affine s b o) (S.image (affine s b)) (f ∘ pull s b) (tariff p*c) := by
  refine ⟨mul_nonneg (tariff_positive _).le hg.1,fun U h x hm hh => ?_⟩
  let m := x.length
  let A : Slab G n m := x.get
  have he := (safe s b U).mp h
  have hF : Germ p.order f (pull s b U) := hf.smooth _ he
  have hE : mixed (f ∘ pull s b) m U A= ∑ i : Fin m → Bool, mixed (f ∘ pull s b) m U (fun j => picked s b (A j) (i j)) := by
    conv_lhs => rw [show A=(fun i => ∑ j:Bool,picked s b (A i) j) from funext fun i => picked_all ..]
    exact (mixed (f ∘ pull s b) m U).map_sum (fun i j => picked s b (A i) j)
  have ht (r : Fin m → Bool) := pure_payment s b U hm hF he hg (fun i => picked s b (A i) (r i)) r
    (fun _ => picked_pure s b _ _) (fun i => picked_bounded s b (hh _ (List.get_mem x i)) _)
  calc
    _ = ‖mixed (f ∘ pull s b) m U A‖ := by rw [← (germs s b U hF).takes A hm]; unfold A; rw [List.ofFn_get]
    _ ≤ ∑ i : Fin m→Bool, ((2:ℝ)^p.power)^m*c := by rw [hE]; exact (norm_sum_le ..).trans (sum_le_sum fun i _ => ht i)
    _ = ((2:ℝ)^m)*(((2:ℝ)^p.power)^m*c) := by simp
    _ ≤ _ := by
      unfold tariff; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hg.1
      apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hm) (pow_le_pow_right₀ (by apply one_le_pow₀; norm_num) hm) (by positivity) (by positivity)
omit [NormedSpace ℝ E] in
lemma mask (U : Config G n) {t : ℝ} {f : Config G n→E} : masked t (S.image (affine s b)) (f ∘ pull s b) U=masked t S f (pull s b U) := by
  by_cases h : Healthy t S (pull s b U)
  · rw [masked_eq _ _ _ _ ((safe s b U).mpr h),masked_eq _ _ _ _ h]; rfl
  rw [masked_ne _ _ _ _ (mt (safe s b U).mp h),masked_ne _ _ _ _ h]

variable {f : Config G n → ℂ} (r : Bool)
def turn (x : ℂ) := if r then star x else x
def turnL : ℂ ≃L[ℝ] ℂ := if r then starL' ℝ else ContinuousLinearEquiv.refl ℝ ℂ
lemma turn_apply : turn r=(turnL r) := by cases r <;> rfl
@[simp] lemma turn_mul (x y) : turn r (x*y) = turn r x * turn r y := by cases r <;> simp [turn]
@[simp] lemma turn_real (x : ℝ) : turn r (x:ℂ)=(x:ℂ) := by cases r <;> simp [turn]
@[simp] lemma turn_powR (x : ℝ) (n : ℕ) : turn r ((x:ℂ)^n)=(x:ℂ)^n := by rw [← Complex.ofReal_pow,turn_real,Complex.ofReal_pow]
@[simp] lemma turn_add (x y) : turn r (x+y)=turn r x+turn r y := by rw [turn_apply]; simp
@[simp] lemma turn_sub (x y) : turn r (x-y)=turn r x-turn r y := by rw [turn_apply]; simp
@[simp] lemma turn_zero : turn r 0=0 := by simp [turn_apply]
@[simp] lemma turn_inj {x} : turn r x=0 ↔ x=0 := by rw [turn_apply]; simp
@[simp] lemma turn_price (x) : ‖turn r x‖=‖x‖ := by cases r <;> simp [turn]





end YM.WardBin.Wheels

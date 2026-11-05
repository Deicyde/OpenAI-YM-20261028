import Mathlib.Analysis.PSeries
import YM.Bid.Town
import YM.Next.STATIONARY.Spectral.ComplexGap



set_option autoImplicit false
/-! # Fine comparison field. Auxiliary mass duplicates initial-site slot.
Thus UNSIGNED permutations mandatory, not rotation at reversed links. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- projection with physical orientation

def copiesV (a : Axis) (G : Gauge) (n : Side) : Link G n →L[ℝ] BaseSites G n :=
    gaugeColor.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (φ:=fun _ : Edge (Site n) => G.Color) (i,a)) ∘L edgeColor.toContinuousLinearMap
lemma notes_u (a : Axis) (x : Link G n) (i) : gaugeColor (copiesV a _ _ x) i=edgeColor x (i,a) := by simp [copiesV]

def stagehand (a : Axis) (G : Gauge) (n : Side) := billsM (pocket _) (pocket _) (copiesV a G n)
def brigadeM (U : Funds (Lines G n 0)) := ∑ i : Axis, ((stagehand i G n)ᵀ*U) *stagehand i G n
lemma brigade_pair (U : Funds (Lines G n 0)) (x y : Link G n) :
    dotProduct x (brigadeM U *ᵥ y) = ∑ i : Axis, dotProduct (copiesV i _ _ x) (U *ᵥ (copiesV i _ _ y)) := by
  unfold brigadeM
  -- distribute
  rw [sum_mulVec]
  simp_rw [dotProduct_sum,both_cost,stagehand,bill_pay]
lemma relic_pos {U : Funds (Lines G n 0)} (h : U.PosDef) : (brigadeM U).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · have he : (brigadeM U).PosSemidef := Matrix.posSemidef_sum _ (fun i hi => h.posSemidef.conjTranspose_mul_mul_same (stagehand i _ _))
    exact he.isHermitian
  intro x hx; rw [star_trivial]; rw [brigade_pair]
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · simpa only [star_trivial] using h.posSemidef.dotProduct_mulVec_nonneg (copiesV i _ _ x)
  have he : ∃ i, copiesV i _ _ x≠0 := by
    by_contra! hb
    apply hx; apply edgeColor.injective; funext i
    rw [← notes_u i.2, hb,map_zero, map_zero]; rfl
  obtain ⟨i,hi⟩ := he
  exact ⟨i,Finset.mem_univ _,by simpa only [star_trivial] using h.dotProduct_mulVec_pos hi⟩

variable (U : Config G n) (p : Clip) (R : PathData G) (μ : ℝ)
def rankAux := flare p R U + mail U*(mail U)ᵀ+ brigadeM (cannon μ U)
def fineMag := (1/2:ℝ)*Real.log (rankAux U p R μ).det - Real.log (grenade μ U).det

lemma rank_memo {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {T : X → Config G n}
    (h : Army T 0) (he : T 0=1) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (hg : 0<μ) : Memo (fun x => rankAux (T x) p R μ) 0 := by
  obtain ⟨hi,hv,_⟩ := memo_flash hg h
  have ht : Memo (fun x => brigadeM (cannon μ (T x))) 0 := by
    unfold brigadeM; intro i j; simp_rw [Matrix.sum_apply]
    refine ContDiffAt.sum fun k _ => ((Memo.raw (stagehand k G n) (0:X)).spot.cross hv |>.cross (Memo.raw (stagehand k G n) (0:X))) i j
  exact ((Memo.twice (memo_damage (pocket (Lines G n 1)) (F:=fun x => burn p R (T x)) (blaze_fire T p R hp h he)) (hi.cross hi.spot))).twice ht

section funded
variable {p R} (k : Coats G n) {B : Bed} {a b σ C Λ : ℝ} (h : R.Bounds p σ C Λ) (ht : Floor B p n a b)
  (hp : Attached B R) (hs : Bid.Sworn B n G)

include h hp hs ht
lemma flare_matches : flare p R (1:Config G n)=billsM (pocket _) (pocket _) (uniformM (G:=G) (Precision.K (B.metric.acts n))) := by
  have hh : Army (input G n) 0 := Army.powL contDiffAt_id
  have hv : ContDiffAt ℝ 2 (intended p R (m:=n)) 0 := ((Work.F02.answer _ _ _ _ _ _ h).crown _ _ _ (input_zero ..) hh).of_le le_top
  apply testers; intro x y
  unfold flare
  rw [bill_pay, show burn p R (1:Config G n)=intended p R from funext (fun x => by simp [burn,intended])]
  have he := detracts (pocket (Lines G n 1)) (intended p R) 0 x y
  rw [cash_pocket,cash_pocket] at he
  rw [he,dotKin]
  refine (Work.F03.hessian_of_limit hv (Q:=fun x y => Bid.gaugeFiscal B (arm G n 1 x) (arm G n 1 y)) (fun z => ?_) ?_ ?_).2.2 x y
  · unfold intended input
    simp_rw [map_smul]; exact Work.F03.main_limit h hp ht hs _
  · intro x y z; rw [map_add,Work.F03.gaugeFiscal_add]
  intro x y; rw [Work.F03.metric_pair B h hp _ _ ht,Work.F03.metric_pair B h hp _ _ ht]; exact sum_congr rfl fun i _ => by rw [real_inner_comm (Work.F03.faceCurl i (arm G n 1 x)), real_inner_comm (Work.F03.ellLine R i (arm G n 1 x))]
lemma rank_positive (hg : 0<μ) : (rankAux (1:Config G n) p R μ).PosDef := by
  unfold rankAux
  have hv : (flare p R (1:Config G n)).PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · have hi : Army (fun x : Link G n => input G n x * 1) 0 := (Army.powL contDiffAt_id).mul (Army.park _ _)
      have he : (flare p R (1:Config G n))ᵀ=flare p R 1 :=
          damage_symm (pocket (Lines G n 1)) (F:=burn p R (1:Config G n)) ((Work.F02.answer _ _ _ _ _ _ h).crown (0:Link G n) n _ (by simp) hi)
      exact he
    intro x
    rw [flare_matches h ht hp hs,bill_pay,star_trivial,dotKin,Work.F03.metric_pair B h hp _ _ ht]; refine Finset.sum_nonneg fun i _ => ?_
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have h := p.quadratic_pos; positivity
  exact PosDef.posSemidef_add (hv.add (posSemidef_self_mul_conjTranspose _)) (relic_pos (cannon_safe _ hg))
end funded
end YM.Stationary
end

/-! # Ward proof for FINE rank auxiliary. Only unsigned permutations
and gauges needed. No log bound from this argument. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

variable (U : Config G n) (p : Clip) (R : PathData G) (μ : ℝ)
lemma rank_respect (hx : 0<μ) {P Q} (hp : Military P) (hq : Military Q)
    (s : Equiv.Perm Axis) (V : Config G n) (he : mail V * P=Q*mail U) (h : Qᵀ * flare p R V * Q=flare p R U)
    (hs : ∀ i : Axis, stagehand i G n * Q = P *stagehand (s i) G n) :
    fineMag V p R μ = fineMag U p R μ := by
  have hu := artillery U hx V hp hq he
  have hh : Qᵀ * rankAux V p R μ *Q = rankAux U p R μ := by
    rw [rankAux,Matrix.mul_add,Matrix.add_mul,Matrix.mul_add,Matrix.add_mul,h,rankAux]; refine congr_arg₂ _ ?_ ?_
    · apply congr_arg
      have H := gram_bend _ _ _ hp (hp.transpose_cross hq he)
      simpa only [transpose_transpose] using H
    unfold brigadeM; rw [Finset.mul_sum,Finset.sum_mul]; conv_rhs => rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun i _ => ?_
    let D := stagehand i G n
    let F := cannon μ V
    change Qᵀ*(Dᵀ*F*D)*Q=_
    have hg : D*Q=P*stagehand (s i) G n := hs i
    rw [show Qᵀ*(Dᵀ*F*D)*Q=(D*Q)ᵀ*F*(D*Q) by rw [transpose_mul]; simp only [Matrix.mul_assoc],hg,transpose_mul]
    have ht := hp.back hu.1; rw [← ht]; unfold F; simp only [Matrix.mul_assoc]
  rw [fineMag,fineMag, hq.turn_det hh,hp.turn_det (hp.back hu.2)]
lemma rank_gauge (hμ : 0<μ) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (k : Coats G n)
    (hv : ContDiffAt ℝ ω (burn p R (Lattice.gauge k U)) 0) : fineMag (Lattice.gauge k U) p R μ=fineMag U p R μ := by
  apply rank_respect U _ _ _ hμ (troop_orthogonal k) (trench_orthogonal k) 1 _ (mail_carry k U) (flare_carry k hp U hv)
  intro i; refine testers fun a b => ?_; simp only [← Matrix.mulVec_mulVec,trench,stagehand,bill_pay,troop, Equiv.Perm.one_apply]
  have he : copiesV i G n (armor k b)=armorG k (copiesV i G n b) := by
    apply gaugeColor.injective; funext i; rw [notes_u,armorG_at,armor_at,notes_u]
  rw [he]
lemma rank_shape (hμ : 0<μ) (s : Signed) (h : ∀ i, s.flip i=false)
    (he : ContDiffAt ℝ ω (burn p R (pull s 0 U)) 0) : fineMag (pull s 0 U) p R μ=fineMag U p R μ := by
  have hF : burn p R (pull s 0 U) ∘ (spiral s U)=burn p R U := by funext x; rw [Function.comp_apply,burn,← wheel]; exact orbit_axis (fun b => quadratic p R b + uncut R.cubic b+uncut R.quartic b) _ _
  refine rank_respect U _ _ _ hμ (brigade s) (bridle s U) s.perm _ (swirl s U) (Eq.trans (damage_rate _ _ _ (spiral s U) he |>.symm) ?_) ?_
  · rw [hF]; rfl
  intro i; refine testers fun a b => ?_; simp only [← Matrix.mulVec_mulVec,regimentG,regimentU,stagehand,bill_pay]
  have he : copiesV i G n (spiral s U b)=switchM s (copiesV (s.perm i) G n b) := by
    apply gaugeColor.injective; funext j; rw [notes_u,rewind, rotate_color,notes_u]
    simp [sendEdge,h,Step.used,Step.rotate,posDir,affine]
  rw [he]

def PoleTest (x : Link G n) := fineMag (input G n x) p R μ

lemma pole_flip {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (he : 0<μ) (s : Signed) (h : ∀ i,s.flip i=false) : PoleTest (n:=n) p R μ ∘ orderTurn s =ᶠ[𝓝 0] PoleTest p R μ := by
  let T := orderTurn (G:=G) (m:=n) s
  have hm : Army (fun v : Link G n => input _ _ (T v)) 0 := Army.powL T.contDiff.contDiffAt
  have ht := blaze_fire _ _ _ hp hm (by simp)
  filter_upwards [(show Tendsto (fun z => (z,(0:Link G n))) (𝓝 (0:Link G n)) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (ht.eventually (by simp))] with a ha
  have heq : input G n (T a)=pull s 0 (input G n a) := (flip_links s a).symm
  have hx : ContDiffAt ℝ ω (burn p R (input G n (T a))) 0 := Work.F05.hold_jet (V:=fun i => burn p R (input G n (T i))) ha
  rw [heq] at hx
  change fineMag (input G n (T a)) _ _ _ = _
  rw [heq]; exact rank_shape _ _ _ _ he s h hx
lemma pole_colored {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (he : 0<μ) : Stained G (PoleTest (n:=n) p R μ) := by
  intro u
  let T := stain (m:=n) u
  have hm : Army (fun v : Link G n => input _ _ (T v)) 0 := Army.powL T.contDiff.contDiffAt
  have ht := blaze_fire _ _ _ hp hm (by simp)
  filter_upwards [(show Tendsto (fun z => (z,(0:Link G n))) (𝓝 (0:Link G n)) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (ht.eventually (by simp))] with a ha
  have heq : input G n (T a)=Lattice.gauge (solid u) (input G n a) := (stain_cons u a).symm
  have hx : ContDiffAt ℝ ω (burn p R (input G n (T a))) 0 := Work.F05.hold_jet (V:=fun i => burn p R (input G n (T i))) ha
  rw [heq] at hx
  change fineMag (input G n (T a)) _ _ _ = _
  rw [heq]; exact rank_gauge _ _ _ _ he hp _ hx
lemma pole_green {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (he : 0<μ) : force (PoleTest p R μ (n:=n)) := by
  let T := moveField (G:=G) (m:=n)
  have hm : Army (fun v : Swatch G n => input _ _ (T v)) 0 := Army.powL moveField_analytic.contDiffAt
  have ht := blaze_fire _ _ _ hp hm (by unfold T; simp)
  filter_upwards [moveField_germ (G:=G) (m:=n),(show Tendsto (fun z => (z,(0:Link G n))) (𝓝 (0:Swatch G n)) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (ht.eventually (by simp))] with a hv ha
  have heq : input G n (T a)=Lattice.gauge (switchSite a.1) (input G n a.2) := hv
  have hx : ContDiffAt ℝ ω (burn p R (input G n (T a))) 0 := Work.F05.hold_jet (V:=fun i => burn p R (input G n (T i))) ha
  rw [heq] at hx
  change fineMag (input G n (T a)) _ _ _ = _
  rw [heq]; exact rank_gauge _ _ _ _ he hp _ hx

lemma pole_peaks (hG : G.Simple) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (he : 0<μ) (hv : IsUnit (rankAux (1:Config G n) p R μ)) :
    ContDiffAt ℝ ω (PoleTest p R μ (n:=n)) 0 ∧ fderiv ℝ (PoleTest p R μ (n:=n)) 0=0 := by
  have hm : Army (input G n) 0 := Army.powL contDiffAt_id
  have hu : ContDiffAt ℝ ω (PoleTest p R μ (n:=n)) 0 :=
    ContDiffAt.sub (ContDiffAt.mul contDiffAt_const ((Memo.det_val (rank_memo p R μ hm (input_zero ..) hp he)).log (by rw [input_zero]; exact ((Matrix.isUnit_iff_isUnit_det _).mp hv).ne_zero)))
      ((Memo.det_val (memo_flash he hm |>.2.2)).log (grenade_safe _ he).det_pos.ne')
  refine ⟨hu,?_⟩
  apply ContinuousLinearMap.ext; intro x
  exact oneFlag hG (fderiv ℝ (PoleTest p R μ) 0) (fun u v => by rw [← tincture]; exact chain_fixed _ (pole_colored _ _ _ hp he u) (hu.differentiableAt (by simp)) v) x
end YM.Stationary
end

/-!
# Positive-channel Γ, auxiliary precision M at flat. Commit to film permits
but use stock symbol for annulus tests. Progress on ARITH after L. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {L n : Side} {p : Momentum} {σ η C D A μ κ : ℝ}
section primer
lemma bingo_pull (a : Axis) (v : Link G n) (i : Lines G n 0) :
    ((stagehand a G n)*ᵥ v) i=v (i.1,coord a,i.2.2) := by
  rw [stagehand,bill_pay];
  rcases i with ⟨i,b,j⟩; rw [vac_only b]; exact congr_arg (fun x : G.Color => x j) (notes_u a v i)

def dasher (G : Gauge) (a : Axis) : CompM (Loc G 0) (Loc G 1) := Matrix.of fun i j => if j=(coord a,i.2) then 1 else 0
lemma dash_up (v : Phase (Loc G 1)) (a) (i) : (dasher G a *ᵥ v) i=v (coord a,i.2) := by simp [dasher, Matrix.mulVec,dotProduct,ite_mul]
lemma dash_down (v : Phase (Loc G 0)) (a) (i) (j : G.ColorIndex) : ((dasher G a)ᵀ *ᵥ v) (coord i,j)=if i=a then v (vac,j) else 0 := by
  have hp : ∀ i j : Axis, coord i=coord j ↔ i=j := fun _ _ => axisEquiv.injective.eq_iff
  simp only [Matrix.mulVec, dotProduct,Matrix.transpose_apply,dasher, Matrix.of_apply,Prod.mk.injEq,hp]
  rw [Fintype.sum_prod_type]; by_cases h : i=a <;> simp [ite_mul, h]
  rw [sum_eq_single vac] <;> simp [vac_only]
lemma dash_far (a) : Jaunt (m:=n) (approached (stagehand a G n)) (fun _ => dasher G a) 0 := by
  have ht (v : Phase (Lines G n 1)) (i : Lines G n 0) : (approached (stagehand a G n) *ᵥ v) i=v (i.1,coord a,i.2.2) := by
    refine Leads.buys (p:=fun v => (approached (stagehand a G n)*ᵥ v) i) (fun x y => congr_fun (Leads.byVec _ x y) i) (q:=fun v => v (i.1,coord a,i.2.2)) (fun x y => rfl) (fun p => ?_) v
    simp only [prom_vec,axes,bingo_pull]
  intro p r h v; rw [add_zero]; ext ⟨i,j,k⟩; change _= tune p (dasher G a *ᵥ v) (i,j,k)
  simp only [ht,tune,dash_up]
lemma bingo (K : Momentum→ℂ) {U : Funds (Lines G n 0)} (h : Jaunt (approached U) (fun p => K p • 1) 0) : Jaunt (approached (brigadeM U)) (fun p => K p • 1) 0 := by
  let f := fun i => ((stagehand i G n)ᵀ*U)*stagehand i G n
  let F := fun p => K p • (1:CompM (Loc G 0) (Loc G 0))
  let E (i : Axis) p := ((dasher G i)ᵀ * F p)* dasher G i
  have he a : Jaunt (approached (f a)) (E a) 0 := by
    unfold f; rw [prom_mul,prom_mul]; exact (((dash_far a).takes.hoist h).hoist (dash_far a))
  intro p q hp v
  have hx : approached (brigadeM U)=∑ i,approached (f i) := by ext; simp [f,approached,Matrix.sum_apply,brigadeM]
  rw [hx,Matrix.sum_mulVec]; ext ⟨x,a,b⟩
  obtain ⟨i,rfl⟩ := axisEquiv.surjective a
  rw [Finset.sum_apply]; simp_rw [he _ p q hp]; change ∑ j: Axis, cell (p+0) x*(E j q*ᵥ v) (coord i,b)=cell (p+0) x*_
  have H j : (E j q *ᵥ v) (coord i,b)= if i=j then K q*v (coord i,b) else 0 := by
    unfold E F; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,dash_down, Matrix.smul_mulVec,one_mulVec]; split <;> rename_i he; · simp [dash_up,he]
    rfl
  simp_rw [H]; simp [Matrix.smul_mulVec]
end primer

def dais (G : Gauge) (μ : ℝ) (B : Bed) (p : Momentum) := rug G B p + pageD G 0 p*(pageD G 0 (-p))ᵀ+ satin μ p • 1

lemma daisy (h : 0 < μ) (k : Clip) (X : PathData G) (B : Bed) {b V D' K' : ℝ}
    (hv : X.Bounds k b K' V) (hp : Attached B X) (he : Floor B k n C D') (hu : Bid.Sworn B n G) (ht : B.metric.safe) :
    Jaunt (approached (rankAux (1:Config G n) k X μ)) (dais G μ B) 0 := by
  unfold rankAux; rw [prom_addition,prom_addition, flare_matches hv he hp hu,mailed_zero, transpose_neg, Matrix.neg_mul, Matrix.mul_neg,neg_neg,prom_mul]
  exact ((rug_plane n B ht).plus ((page_read n 0).hoist (page_read n 0 |>.takes))).plus (bingo _ (tonic_cannon n h))
end YM.Stationary
end

/-!
# Rank/gauge reference with same analytic budget basis. Tilt singular
only with available routes. Supplies uniforms pre-L. Extra tensor T^3
trace ideal used later with same law. No gauge clipping at harmonic. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L : Side} {α β : Type} [Fintype α] [DecidableEq α]
    {σ η ε μ A B Z : ℝ} {p : Momentum}
-- coerce at each static alias. fine Continuum invest via stone.
lemma throne_floor (x : Phase (Loc G 0)) (hp : star p=p) (h : 0<μ) :
    (1/(2^10):ℝ)*pebWeight p μ * slug x^2 ≤ (dotProduct (star x) (throneF G μ p*ᵥ x)).re := by
  let i : ℝ := shadeK p^2 + μ^2*(μ^2*(pebWeight p μ)⁻¹)^9
  have he : 0≤ i := by unfold i; positivity [peb_pos p h]
  have hi : throne μ p=(i:ℂ) := by unfold throne satin damp soda i pebWeight; rw [stone_real hp]; push_cast; rfl
  have H := throne_pays hp h; rw [hi,norm_real,Real.norm_of_nonneg he] at H
  apply (mul_le_mul_of_nonneg_right H (sq_nonneg _)).trans
  unfold throneF; rw [Matrix.smul_mulVec,one_mulVec,dotProduct_smul,slug_self,hi]
  simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im, zero_mul,sub_zero]; rfl
lemma dais_floor (hp : star p=p) (w : Clip) (K : Bed) (h : 0<μ) (x : Phase (Loc G 1))
    (hv : K.metric.strip σ A) (he : 0<σ) (hy : ∀ n, Floor K w n ε Z) (hb : 0<ε) :
    (min ε 1)/(2^10:ℝ)*pebWeight p μ *slug x^2 ≤ (dotProduct (star x) (dais G μ K p *ᵥ x)).re := by
  have H := rug_test hv he hy hp x
  rw [dais,Matrix.add_mulVec,Matrix.add_mulVec, dotProduct_add,dotProduct_add]
  simp only [Complex.add_re]
  let n : ℝ := μ^2*(μ^2*(shadeK p^2+μ^2)⁻¹)^9
  have ht : satin μ p= (n:ℂ) := by unfold n satin damp soda; rw [stone_real hp]; push_cast; rfl
  rw [Matrix.smul_mulVec,one_mulVec,dotProduct_smul,slug_self,ht,smul_eq_mul]
  simp only [mul_re,ofReal_re,ofReal_im, zero_mul,sub_zero]
  let U := pageD G 0 p
  have hx : (dotProduct (star x) ((U*(pageD G 0 (-p))ᵀ) *ᵥ x)).re=slug (Uᴴ *ᵥ x)^2 := by
    rw [← Matrix.mulVec_mulVec,page_rear _ hp, ← show Uᴴᴴ= U from Matrix.conjTranspose_conjTranspose U,vested, conjTranspose_conjTranspose,slug_self]
    rfl
  rw [hx]
  have hq := throne_pays hp h
  have hn : 0 ≤ n := by unfold n; positivity
  rw [throne,ht,stone_real hp,← Complex.ofReal_add, norm_real,Real.norm_of_nonneg (add_nonneg (sq_nonneg _) hn)] at hq
  let k := min ε 1
  have hK : 0<k := lt_min hb zero_lt_one
  have hy : k ≤ 1 := min_le_right ..; have hh : k ≤ ε := min_le_left ..
  have he' : (shadeK p^2+n)*slug x^2 = slug (Uᴴ *ᵥ x)^2 + slug (pageD G 1 p *ᵥ x)^2 + n*slug x^2 := by rw [pure_grade hp G x, add_mul,mul_pow]
  calc
    _ = k * ((1/(2^10):ℝ)*pebWeight p μ * slug x^2) := by unfold k; ring
    _ ≤ k *((shadeK p^2+n)*slug x^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq (sq_nonneg _)) hK.le
    _ ≤ _ := by
      rw [he']; nlinarith only [H, hy,hh,sq_nonneg (slug (Uᴴ *ᵥ x)),sq_nonneg (slug (pageD G 1 p*ᵥ x)), mul_nonneg hn (sq_nonneg (slug x))]

-- single per-alias variance sufficient
lemma FoldStable (p : Momentum) (U : Momentum→CompM α α) (hp : star p=p) (h : ∀ i : Site L,∀ x : Phase α, ε*pebWeight (aliasAt p i) (inch L) * slug x^2 ≤ (dotProduct (star x) (U (aliasAt p i) *ᵥ x)).re) :
    Stable (carryM ((altarTile L α).dual) (altarTile L α) p p (furnish L U p)) ε := by
  let S := altarTile L α
  apply stable_real; intro i
  let v := S.tile p *ᵥ i
  let T := plankTile L α p
  rw [← S.pole (tiles_pair hp) (furnish L U p), sleeve p hp]
  change ε* slug i^2≤(∑ j : Site L,(dotProduct (star (stackSlice j (crewAlias p v))) _)).re
  have he := rate_sq_tile p (crewAlias p v); rw [tile_crew, show (altarTile L α).rate p v=slug i from Slab.cover_rate ..] at he
  rw [he, mul_sum,re_sum]; apply sum_le_sum
  intro j _; have H := h j (stackSlice j (crewAlias p v)); rw [← mul_assoc,hill_sq]; exact H

-- hold w ≤ 1/128.
lemma soda_pay_t (h : 0<μ) (he : μ≤1) (hp : p∈strip (μ*(1/128))) : ‖damp μ p‖ ≤ 2 := by
  have hz : (1/2:ℝ)* μ^2 ≤ ‖soda μ p‖ := le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (by norm_num : 0 ≤ (1/2:ℝ))) (soda_safe_cube h he hp)
  rw [damp,norm_mul,norm_inv, ← div_eq_mul_inv,div_le_iff₀ (by nlinarith only [pow_pos h 2,hz]),norm_pow,norm_real,Real.norm_of_nonneg h.le]; linarith
lemma satin_prices (h : 0<μ) (he : μ≤1) (hp : p∈strip (μ*(1/128))) : ‖satin μ p‖ ≤ μ^2*2^9 := by
  unfold satin; rw [norm_mul,norm_pow,norm_pow,norm_real,Real.norm_of_nonneg h.le]; gcongr; exact soda_pay_t h he hp
lemma satin_contours (hs : 0<μ) (he : μ≤1) : Poster (μ*(1/128)) (fun p : Momentum => satin μ p • (1:CompM α α)) := by
  refine ⟨fun {p} hp i j => ?_,fun {p q} hp h => ?_⟩
  ·
    change DifferentiableAt ℂ (fun p => satin μ p * _) _
    refine (DifferentiableAt.mul ?_ (differentiableAt_const _)); unfold satin damp; refine DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.pow ?_ _)
    refine DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.inv (h:=soda μ) ?_ (soda_glass hs he hp)); unfold soda stone dotProduct Exterior.q; fun_prop
  unfold satin damp; rw [soda_roll hp]
lemma dais_charge (K : Bed) (he : 0<μ) (hu : μ≤1) (hs : 0<σ) (hv : σ≤μ*(1/128)) (h : K.metric.strip σ A) : Poster σ (dais G μ K) :=
    ((rug_played K h hs).amounts ((page_linen 0 (G:=G)).forge ((page_linen 0).reverse))).amounts ((satin_contours he hu).skinny hv)

lemma cold_t (G : Gauge) (i : ℕ) (l : Site L) (h : p∈strip 1) :
    vflux (pageD G i (aliasAt p l)) ≤ pageTax G i*(5*hill p l) ∧ vflux (pageD G i (-aliasAt p l))≤pageTax G i*(5*hill p l) := by
  have hc : 0≤pageTax G i := mul_nonneg fest_pos (by norm_num)
  refine ⟨(page_tax ..).trans (mul_le_mul_of_nonneg_left (hill_tilt _ h) hc),?_⟩
  rw [show pageD G i (-aliasAt p l)=pageD G i (aliasAt (-p) (-l)) from (congr_arg (tintedLocal G) (rolls_symbol (alias_counter p l) i)).symm, ← hill_turn p l]
  exact (page_tax ..).trans (mul_le_mul_of_nonneg_left (hill_tilt _ (negResident h)) hc)

lemma Fold_upper (L : Side) (K : Bed) (hp : K.metric.strip (inch L*σ) A) (hr : p∈strip σ) (hv : σ≤1/128) (hk : 0 ≤ A) : serial (altarTile L (Loc G 1)|>.dual) (altarTile L _) p p
    (furnish L (dais G (inch L) K) p) (bridgeCost G A + (pageTax G 0 * 5)^2+2^9) := by
  have he : σ≤1 := by linarith
  have ht : 0≤pageTax G 1 := mul_nonneg fest_pos (by norm_num)
  refine woven_price _ (by have h : 0 ≤ bridgeCost G A := mul_nonneg (sq_nonneg _) (mul_nonneg fest_pos hk); positivity) fun l => ?_
  have hr' : p∈strip (1/128) := fun i => (hr i).trans_le hv; have hz : p∈strip 1 := fun i => (hr i).trans_le he
  let k := aliasAt p l; let u := hill p l
  have hs := fareH (G:=G) (alias_inside hr l) hp hk
  have hn : vflux (rug G K k) ≤ bridgeCost G A*u^2 := by
    obtain ⟨h1,h2⟩ := cold_t G 1 l hz
    unfold rug; apply (flux_power ..).trans
    refine (mul_le_mul ((flux_power ..).trans (mul_le_mul ((back_flux ..).trans_le h2) hs (flux_nonneg _) ((flux_nonneg _).trans h2))) h1 (flux_nonneg _) (mul_nonneg ((flux_nonneg _).trans h2) ((flux_nonneg _).trans hs))).trans_eq ?_
    unfold u bridgeCost; ring
  have hm := satin_prices (inch_pos L) (inch_le L) (alias_inside hr' l)
  have hi : vflux (satin (inch L) k • (1:CompM (Loc G 1) (Loc G 1))) ≤ 2^9*u^2 := by
    rw [flux_cost]; apply (mul_le_of_le_one_right (norm_nonneg _) flux_one).trans; refine hm.trans ?_; rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inch_pos _).le (hill_inch _ l) _) (by positivity)
  unfold dais
  obtain ⟨h1,h2⟩ := cold_t G 0 l hz
  have hj : vflux (pageD G 0 k * (pageD G 0 (-k))ᵀ) ≤ (pageTax G 0 * 5)^2*u^2 := by
    refine ((flux_power ..).trans (mul_le_mul h1 ((back_flux ..).trans_le h2) (flux_nonneg _) ((flux_nonneg _).trans h1))).trans_eq ?_
    unfold u; ring
  rw [add_mul,add_mul]; exact (flux_plus ..).trans (add_le_add ((flux_plus ..).trans (add_le_add hn hj)) hi)
end YM.Stationary
end

/-!
# Coarse strip supplied inverses for reference and ghosts.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {L : Side} {p : Momentum} {σ η ε μ A C : ℝ}

lemma stone_shade (l : Site L) (h : p∈strip 1) : ‖stone (aliasAt p l)‖ ≤ 25*(hill p l)^2 := by
  apply (slug_dot ..).trans
  have hp := hill_tilt l h; have hv := hill_tilt (L:=L) (-l) (negResident h)
  rw [hill_turn] at hv
  have he : Exterior.q (aliasAt (-p) (-l))=Exterior.q (-aliasAt p l) := by
    ext1 i; unfold Exterior.q; rw [← factor,← factor,(alias_counter p l).exp]
  rw [he] at hv; exact (mul_le_mul hv hp (slug_nonneg _) ((slug_nonneg _).trans hv)).trans_eq (by ring)

lemma throne_folded (h : p∈strip (1/128:ℝ)) : serial (altarTile L (Loc G 0)|>.dual) (altarTile L _) p p (throneK G L p) (25+2^9) := by
  have ht : p∈strip 1 := fun i => lt_trans (h i) (by norm_num)
  refine woven_price _ (by norm_num) fun l => ?_
  unfold throneF; rw [flux_cost];
  refine (mul_le_of_le_one_right (norm_nonneg _) flux_one).trans ((norm_add_le ..).trans ?_)
  rw [add_mul]
  refine add_le_add (stone_shade l ht) ((satin_prices (inch_pos L) (inch_le L) (alias_inside h l)).trans ?_); rw [mul_comm]; have he := inch_pos L; gcongr; exact hill_inch p l

lemma chillThrone (G : Gauge) : ∃ η C,0<η∧η≤(1/128:ℝ)∧0≤C∧∀ L : Side,
    Freezer (altarTile L (Loc G 0)|>.dual) (altarTile L _) (throneK G L) η C := by
  let a : ℝ := 1/2^10
  obtain ⟨η,C,ht,hq,hC,K⟩ := shelter (1/128) (25+2^9) 6 a (by norm_num) (by norm_num) (by norm_num) (by norm_num [a])
  refine ⟨η,C,ht,hq,hC,fun L => ?_⟩
  let S := altarTile L (Loc G 0)
  have hp : S.Height (1/128) 6 := (altar_range ..).mono (by norm_num) le_rfl
  exact K _ S.dual S hp.dual hp _ ((throne_rate (G:=G) (inch_pos L) (inch_le L)).furnish_ok) (fun p hp => throne_folded hp) (fun p hp => FoldStable _ _ hp (fun i x => throne_floor x (by rw [← alias_conj,hp]) (inch_pos _)))

lemma chillDais (G : Gauge) (hs : 0<σ) (hσ : σ≤1/128) (ha : 0≤A) (hε : 0<ε) :
    ∃ η C,0<η∧η≤σ∧0≤C∧∀ (L : Side) (B : Bed) (w : Clip) (pt : ℝ), B.metric.strip (inch L*σ) A →
       (∀ n, Floor B w n ε pt) →
        Freezer (altarTile L (Loc G 1)|>.dual) (altarTile L _) (furnish L (dais G (inch L) B)) η C := by
  have h : 0 ≤ bridgeCost G A := mul_nonneg (sq_nonneg _) (mul_nonneg fest_pos ha)
  let u := bridgeCost G A + (pageTax G 0 * 5)^2+2^9
  obtain ⟨η,C,ht,hq,hC,Q⟩ := shelter σ u 6 ((min ε 1)/(2^10)) hs (by unfold u; positivity) (by norm_num) (by positivity)
  refine ⟨η,C,ht,hq,hC,fun L V w pt hV hv=> ?_⟩
  let S := altarTile L (Loc G 1)
  have hp : S.Height σ 6 := (altar_range ..).mono (by linarith) le_rfl
  have hL := inch_pos L; have he := mul_pos hL hs; have hY := dais_charge (G:=G) V hL (inch_le _) he (mul_le_mul_of_nonneg_left hσ hL.le) hV
  exact Q _ S.dual S hp.dual hp _ hY.furnish_ok (fun p hz => Fold_upper L V hV hz hσ ha) (fun i hi => FoldStable _ _ hi (fun l x => dais_floor (by rw [← alias_conj,hi]) _ V hL x hV he hv hε))

lemma ammo_poster {μ : ℝ} : Poster σ (fun p => soda μ p • (1:CompM (Loc G 0) (Loc G 0))) := by
  refine ⟨fun w _ _ => ?_, fun e _ => congr_arg (· • _) (soda_roll e)⟩; unfold soda stone dotProduct Exterior.q; simp only [Matrix.smul_apply]; fun_prop
lemma ammo_bill (G : Gauge) : ∃ η C,0<η∧η≤(1/128:ℝ) ∧ 0≤C ∧∀ L : Side,
    Freezer (altarTile L (Loc G 0)|>.dual) (altarTile L _) (furnish L (fun p => soda (inch L) p • (1:CompM (Loc G 0) (Loc G 0)))) η C := by
  obtain ⟨η,C,ht,hq,hC,K⟩ := shelter (1/128) 26 6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨η,C,ht,hq,hC,fun L => ?_⟩
  let S := altarTile L (Loc G 0)
  have hp : S.Height (1/128) 6 := (altar_range ..).mono (by norm_num) le_rfl
  refine K _ S.dual S hp.dual hp _ ammo_poster.furnish_ok (fun p h => woven_price _ (by norm_num) fun l => ?_) fun p hp => FoldStable p _ hp fun l v => ?_
  · rw [flux_cost]; refine (mul_le_of_le_one_right (norm_nonneg _) flux_one).trans ?_
    have hx := (show ‖soda (inch L) (aliasAt p l)‖≤_ from norm_add_le (stone _) _); apply hx.trans
    rw [norm_pow,norm_real,Real.norm_of_nonneg (inch_pos _).le]; have hq := pow_le_pow_left₀ (inch_pos L).le (hill_inch p l) 2; linarith [stone_shade l (p:=p) (by intro i; exact (h i).trans (by norm_num))]
  simp only [Matrix.smul_mulVec,one_mulVec,dotProduct_smul,slug_self]
  rw [show soda (inch L) (aliasAt p l)=(↑(pebWeight (aliasAt p l) (inch L)):ℂ) by unfold soda pebWeight; rw [stone_real (by rw [← alias_conj,hp])]; push_cast; rfl]; rw [smul_eq_mul,Complex.mul_re]; simp only [ofReal_re,ofReal_im,zero_mul,sub_zero,one_mul]; exact le_rfl
end YM.Stationary
end

/-!
# Trace ideal for three unscattered massive arcs. `soda` consistent
at vertical & horizontal. Pre-L denominator width paid by fixed curvature.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Pressure
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α] {p : Momentum} {σ C : ℝ} {L : Side}

private lemma ball_tally (L : Side) (n : ℕ) : (univ.filter (fun i : Site L => pdist i = n)).card ≤ (2*n+1)^4 := by
  let V := univ.filter (fun i : Site L => pdist i=n)
  let W := box n
  have ht : W.card=(2*n+1)^4 := by rw [show W=_ from rfl]; unfold W; rw [box_length,Lattice.card_layers]
  rw [← ht]; apply Finset.card_le_card_of_injOn (f:=Lattice.lift)
  · intro i hi; rw [mem_coe,box_test]; constructor <;> intro k <;> have h := component_le i k <;> have hh := (Finset.mem_filter.mp (show i∈V from hi)).2 <;> omega
  exact Function.Injective.injOn (fun x y h => by rw [← wrap_lift x,h,wrap_lift])

private def feeStreet (n : ℕ) := 16 * (((n+1:ℝ)^2)⁻¹)
def jointMoney := ∑' i : ℕ, feeStreet i
private theorem street_quota : Summable feeStreet := by
  have ht := (Real.summable_nat_pow_inv (p:=2)).2 (by decide); unfold feeStreet
  exact Summable.mul_left _ (ht.comp_injective (show Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h) |>.congr (by simp))
lemma touring (L : Side) : ∑ i : Site L, (((pdist i+1:ℝ)^6)⁻¹)≤ jointMoney := by
  let f (i : ℕ) := (((i:ℝ)+1)^6)⁻¹
  let g := pdist (n:=L)
  let Z := (univ : Finset (Site L)).image g
  have he n (i : Site L) : g i=n → f n=f (g i) := fun h => congr_arg f h.symm
  have hv n : ∑ i : Site L, (if n=g i then f n else 0) = (univ.filter (fun i : Site L => g i=n)).card*f n := by rw [← sum_filter, Finset.sum_const,nsmul_eq_mul]; simp only [eq_comm (a:=n)]
  calc
    _ = ∑ j∈Z,∑ i : Site L, (if j=g i then f j else 0) := by rw [sum_comm]; apply sum_congr rfl; intro i _; simp [Z,f]; rfl
    _ ≤ ∑ j∈Z,feeStreet j := sum_le_sum fun j _ => by
      rw [hv]; unfold f
      apply (mul_le_mul_of_nonneg_right (show (((univ.filter (fun i : Site L => g i=j)).card:ℝ)) ≤ (((2*j+1)^4:ℕ):ℝ) by exact_mod_cast ball_tally L j) (by positivity)).trans
      unfold feeStreet; push_cast; rw [← div_eq_mul_inv,← div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
      calc _ ≤ ((2:ℝ)*(j+1))^4*(j+1:ℝ)^2 := by have ht := Nat.cast_nonneg (α:=ℝ) j; gcongr <;> linarith
           _ = _ := by ring
    _ ≤ _ := street_quota.sum_le_tsum _ (fun i _ => by unfold feeStreet; positivity)
lemma thin_pay (p : Momentum) (l : Site L) (hl : Odd L.val) (hp : p∈strip (1/128:ℝ)) (hv : Nave p) : ‖damp (inch L) (aliasAt p l)‖ ≤ 2*((pdist l+1:ℝ)^2)⁻¹ := by
  rcases eq_or_ne l 0 with hl'|hl'
  · subst l
    have h : pdist (0:Site L)=0 := by simp [pdist,Lattice.lift]
    simpa [h] using soda_pay_t (inch_pos L) (inch_le L) (alias_inside hp (0:Site L))
  let η := inch L; have hx : 0<η := inch_pos L
  have hw := hv.heights hl' hl
  let n : ℝ := pdist l; have hn : 1 ≤ n := by unfold n; exact_mod_cast pdist_pos hl'
  have hh : (n+1)*η ≤ shadeK (aliasAt p l) := by unfold n η at *; nlinarith
  let D := ‖soda η (aliasAt p l)‖
  have hd : (1/2:ℝ)*((n+1)*η)^2 ≤ D := (mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ (by positivity) hh 2) (le_add_of_nonneg_right (sq_nonneg _))) (by norm_num)).trans (soda_safe_cube (inch_pos L) (inch_le L) (alias_inside hp l))
  have hD : 0<D := lt_of_lt_of_le (by positivity) hd
  rw [damp,norm_mul,norm_pow,norm_inv, norm_real,Real.norm_of_nonneg (inch_pos L).le]; change η^2 * D⁻¹ ≤ 2*((n+1)^2)⁻¹
  rw [← div_eq_mul_inv,← div_eq_mul_inv, div_le_div_iff₀ hD (by positivity)]; nlinarith only [hd]

lemma budgetRun (L : Side) (hl : Odd L.val) (hp : p ∈ strip (1/128:ℝ)) :
    ∑ l : Site L, ‖damp (inch L) (aliasAt p l)^3‖ ≤ 8*jointMoney := by
  obtain ⟨z,hz,x,H⟩ := Nave.roll p
  subst p
  have hx : z∈strip (1/128:ℝ) := fun j => by simpa [reciprocal] using hp j
  have he : ∀ i j : Momentum, rolls i j → damp (inch L) i=damp (inch L) j := fun i j hp => by unfold damp; rw [soda_roll hp]
  simp_rw [he _ _ (alias_roll z x _)]
  rw [show (∑ i : Site L, ‖damp (inch L) (aliasAt z (i+wrap _ x))^3‖)=_ from Equiv.sum_comp (Equiv.addRight (wrap L x)) (fun i => ‖damp (inch L) (aliasAt z i)^3‖)]
  apply le_trans _ (mul_le_mul_of_nonneg_left (touring L) (by norm_num : (0:ℝ) ≤ 8)); rw [Finset.mul_sum]; apply sum_le_sum; intro j _
  rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) (thin_pay _ j hl hx hz) _).trans_eq (by rw [mul_pow, inv_pow, ← pow_mul]; norm_num)

lemma thin_doubled (L : Side) (hl : Odd L.val) (hp : p∈strip (1/128:ℝ)) :
    bags (Slab.basic _) (Slab.basic _) p p (furnish L (fun q : Momentum => damp (inch L) q^3 • (1:CompM α α)) p)
      ((Real.exp (1/128*4)*((Fintype.card α:ℝ)*(8*jointMoney)))*Real.exp (1/128*4)) := by
  unfold bags carryM Slab.basic; simp only [inv_one,Matrix.one_mul, Matrix.mul_one,furnish]
  let f (l : Co L α) := damp (inch L) (aliasAt p l.1)^3
  rw [show posterBlock L _ p= diagonal f by
    ext ⟨i,a⟩ ⟨j,b⟩; unfold posterBlock fiber; by_cases h : i=j <;> by_cases h1 : a=b <;> simp [f,h,h1, Matrix.one_apply,Matrix.diagonal_apply]]
  have ht : ∑ i, ‖f i‖ ≤ (Fintype.card α:ℝ)*(8*jointMoney) := by rw [Fintype.sum_prod_type]; simp only [f, Finset.sum_const,card_univ,nsmul_eq_mul]; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (budgetRun L hl hp) (Nat.cast_nonneg _)
  exact (((Doubly.diagram f).credit2 ht).duet_top (plank_cap p hp)).duo (plank_back p hp)
end YM.Stationary
end

import YM.Extension.UV.Canon.Actual
import YM.Progress.STATIONARY_SCENES.SliceGap

/-! Fixed-period finite forest matrices on the actual paths. At flat order no representation
comparison required: the marked columns solve a unique restricted system with inherited gap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Function Filter Set Lattice RG Wilson Laurent Exterior Bloch Input Precision Matrix Supply
open Progress.StationaryScenes Tree Bid
open scoped Matrix Topology BigOperators Classical
variable {G:Gauge} {A:Levels G}

section forest
variable {c f : Side} {S:StepData c f} (F:Forest S.ratio)
local notation "ℓ"=> Green.link F
-- principal restriction, no symbolic substitution of complex group links
def cutK (K : Matrix (Body 1 f) (Body 1 f) ℝ) := (K+S.kernel.penalty•((probe S).transpose*probe S)).submatrix ℓ ℓ
def shard (W : Matrix (Body 1 f) (Body 1 c) ℝ) := (extracted S F W).submatrix ℓ id

def matProbe : Matrix F.Free (Body 1 c) ℝ:= (S.kernel.penalty•(probe S).transpose).submatrix ℓ id

lemma trunk_zero (W : Matrix (Body 1 f) (Body 1 c) ℝ) (i) (hi:i∈F.trunks) j : extracted S F W (i.1,coord i.2) j=0:= by
  have h:= stays (S:=S) F W (Pi.single j 1) i hi
  rw [Matrix.mulVec_single_one] at h
  exact h
lemma cut_solve (K : Matrix (Body 1 f) (Body 1 f) ℝ) (W : Matrix (Body 1 f) (Body 1 c) ℝ) :
    (K*extracted S F W).submatrix ℓ id=K.submatrix ℓ ℓ*shard F W:= by
  set Q:=Equiv.prodCongr (Equiv.refl (Site f)) axisEquiv
  have hx i : Q i=(i.1,coord i.2):= rfl
  ext i j
  rw [submatrix_apply,Matrix.mul_apply,Matrix.mul_apply, ← Q.sum_comp (fun z=> K (ℓ i) z * extracted S F W z (id j))]
  let t:Finset (Site f × Axis):= F.trunksᶜ
  let g (k : Site f × Axis) := K (ℓ i) (Q k) * extracted S F W (Q k) j
  have he : (∑ k∈t, g k)=∑ k,g k := Finset.sum_subset (Finset.subset_univ t) fun a ha hb=> by apply mul_eq_zero.mpr; exact Or.inr ((hx a).symm ▸ trunk_zero F _ _ (by simpa [t] using hb) _)
  change ∑ a,g a=_
  rw [← he, Finset.sum_subtype (p:=fun y=> y∉F.trunks) t (by simp [t]) g]
  rfl
lemma formula {Q:Bed} {W'} (R:Towers S.patch.L) (h : Towers.Diagonal S Q W' R) : cutK F (Precision.K (Q.metric.acts f))*shard F (installed S.ratio R.A0)=matProbe F := by
  let U:= installed S.ratio R.A0
  obtain ⟨hP,hA⟩:= stationed F U _ _ h.trial
  rw [cutK,← cut_solve]
  change ((Precision.K (Q.metric.acts f) + (S.kernel.penalty • ((probe S).transpose*probe S) : Matrix _ _ _))*extracted S F U : Matrix _ _ _).submatrix ℓ id = _
  rw [Matrix.add_mul,Matrix.smul_mul,Matrix.mul_assoc,hA,hP,Matrix.mul_sub,smul_sub,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul,Matrix.mul_one,add_sub_cancel,matProbe]
end forest

section matrices
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma bottom_unit (x : Matrix ι ι ℝ) {d:ℝ} (hd : 0<d) (h:Green.Bottom x d): IsUnit x.det:= by
  apply (x.isUnit_iff_isUnit_det).1
  apply Matrix.mulVec_injective_iff_isUnit.1
  intro v w h'
  have hy : x*ᵥ(v-w)=0:= by rw [mulVec_sub,h',sub_self]
  have hh := h (v-w); rw [hy] at hh
  by_contra hne
  obtain ⟨i,hi⟩:= not_forall.mp (mt funext hne)
  have h0 : 0<dotProduct (v-w) (v-w):= Finset.sum_pos' (fun j _=>mul_self_nonneg _) ⟨i,Finset.mem_univ _,mul_self_pos.mpr (sub_ne_zero.mpr hi)⟩
  simp only [dotProduct_zero] at hh; nlinarith [mul_pos hd h0]
lemma limit_inv (x : ℕ → Matrix ι ι ℝ) (y) (hy:Tendsto x atTop (𝓝 y)) (hu:IsUnit y.det): Tendsto (fun n=> (x n)⁻¹) atTop (𝓝 y⁻¹):=by
  have hdet := (Continuous.matrix_det (continuous_id (X:=Matrix ι ι ℝ))).continuousAt.tendsto.comp hy
  have ht:= Tendsto.smul ((hdet).inv₀ (hu.ne_zero)) ((Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp hy)
  convert ht using 1 <;> simp [inv_def,Ring.inverse_eq_inv]
end matrices

section horizon
variable (M:Horizon A) {Z:MapPrices} (hP:M.Suffices Z) {s:Sheet G} {D:Rolls s} {O:ChartRatio G} {P:PostCost D} (kin:Kin M O) (h:kin.Planned P)
variable (hG:G.Simple) (p m:ℕ)
variable (hL:Bid.Larger (G:=G) (A.clock.op m p)) (hS:∀ n,m<n → Bid.Sworn (M.H n (m+1)) (A.S.side (m+1) p) G) (F:Forest (A.clock.op m p).ratio)
def tangent (n:ℕ) := shard (S:=A.clock.op m p) F (installed (A.clock.op m p).ratio (M.towers n m).A0)
set_option maxHeartbeats 310000 in
include hP h hL hS hG in
lemma cut_gap (n) (hn:m<n) : Green.Bottom (cutK (S:=A.clock.op m p) F (Precision.K ((M.H n (m+1)).metric.acts (A.S.side (m+1) p)))) (P.η (A.clock.J (m+1))):=by
  let R:=kin.path n (m+1); let U:=M.H n (m+1); let Q₀:=cutK (S:=A.clock.op m p) F (Precision.K (U.metric.acts (A.S.side (m+1) p)))
  let c:=A.S.side m p; let f:=A.S.side (m+1) p
  let θ:(A.clock.op m p).Choices:= Classical.arbitrary _
  let T:= Precision.hessian F θ (A.params (m+1)).clip R 0 0 -- use arbitrary choice
  have hc := h.cap n (m+1) hn
  have hv := hP.all n (m+1) hn f
  have hm := Work.F03.answer G c f (A.clock.op m p) hL F U (A.params (m+1)).clip R (A.params (m+1)).width (A.params (m+1)).paths (A.clock.loopCap (m+1)) _ _ hv hc (h.links n (m+1) hn) (hS n hn) (Work.F02.answer _ _ _ _ _ _ hc)
  have hx := Green.entries (D:=U) (P:=R) (F:=F) θ hm.1 hm.2
  obtain ⟨i⟩:= Stationary.colorAvail G hG
  intro v
  let y (j : F.Free × G.ColorIndex):= if j.2=i then v j.1 else 0
  have he (a b) : T a b = if a.2=b.2 then Q₀ a.1 b.1 else 0:=hx _ _
  have ha z : T (z,i) ⬝ᵥ y=Q₀ z ⬝ᵥ v:= by simp [dotProduct,y,he,Fintype.sum_prod_type]
  have hp := Green.counted θ (h.gap _ _ _ hn F) y
  change _ ≤ dotProduct y (T *ᵥ y) at hp
  simpa [matProbe,Kactual,dotProduct,y,mulVec,Fintype.sum_prod_type,he,Q₀] using hp

include hP h hL hS hG in
set_option maxHeartbeats 800000 in
lemma tangent_converges (hf:SizeFloor A.clock.kernel.penalty A): ∃ y,Tendsto (tangent M p m F) atTop (𝓝 y):= by
 obtain ⟨x,hx⟩:= K_tendsto M hP hf (m+1) p
 let z:=cutK (S:=A.clock.op m p) F x
 let f n:=Kactual M n (m+1) p
 let w n:=cutK (S:=A.clock.op m p) F (f n)
 have he : Tendsto w atTop (𝓝 z):= by apply ContinuousAt.tendsto (show ContinuousAt (cutK (S:=A.clock.op m p) F) x by unfold cutK; fun_prop) |>.comp hx
 have hb : ∀ᶠ n : ℕ in atTop, Green.Bottom (w n) (P.η (A.clock.J (m+1))):= by filter_upwards [eventually_gt_atTop m] with n hn using cut_gap M hP kin h hG _ _ hL hS F n hn
 have hz : Green.Bottom z (P.η (A.clock.J (m+1))):= fun v=> ge_of_tendsto (ContinuousAt.tendsto (show ContinuousAt (fun A=>v ⬝ᵥ (A *ᵥ v)) z by fun_prop)|>.comp he) (by filter_upwards [hb] with n hn using hn v)
 have hI:= limit_inv w z he (bottom_unit z (P.price _) hz)
 refine ⟨z⁻¹ * matProbe (S:=A.clock.op m p) F,(tendsto_matrix_mul _ _ hI tendsto_const_nhds).congr' ?_⟩
 filter_upwards [hb, eventually_gt_atTop m] with n hn hi
 have hf : w n*tangent M p m F n=matProbe (S:=A.clock.op m p) F:= formula F _ (hP.crossings n m p hi)
 rw [← hf, Matrix.nonsing_inv_mul_cancel_left (w n) _ (bottom_unit _ (P.price _) hn)]


include hP h hL hS hG
set_option maxHeartbeats 500000 in
lemma tangent_vector (hf:SizeFloor A.clock.kernel.penalty A) (x) : ∃ y,Tendsto (fun n=> (fderiv ℝ (kin.stationary n m p F) 0) x) atTop (𝓝 y) := by
  obtain ⟨y,hy⟩:= tangent_converges M hP kin h hG p m hL hS F hf
  let Sp:=A.clock.op m p; let ξ:= Sp.ratio; let c:=A.S.side m p; let f:=A.S.side (m+1) p
  let eval (a:F.Free) (b : Matrix F.Free (Body 1 c) ℝ) : G.Color := WithLp.toLp 2 (fun j : G.ColorIndex => (b *ᵥ parts G 1 x j) a - (linearCopy ξ (collect G x) a.1) j)
  have hv n (hn:m<n): (fderiv ℝ (kin.stationary n m p F) 0) x=fun a=> eval a (tangent M p m F n) := by
    let ρ:=kin.stationary n m p F
    obtain ⟨hq,hx⟩:=h.critical n m p hn F
    have hx' := hx x
    have he : HasFDerivAt ρ (fderiv ℝ ρ 0) ((fun t : ℝ=> t • x) 0):=(zero_smul ℝ x).symm ▸ (hq.2.1.differentiableAt (by simp)).hasFDerivAt
    have hh := he.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ) |>.smul_const x))
    rw [one_smul] at hh
    refine (hh.unique (by exact hx')).trans ?_
    ext a j
    rfl
  refine ⟨fun a=>eval a y,tendsto_pi_nhds.mpr fun a=> ?_⟩
  have he : Tendsto (eval a ∘ tangent M p m F) atTop (𝓝 (eval a y)):= Filter.Tendsto.comp (f:=tangent M p m F) (ContinuousAt.tendsto <| by unfold eval; exact (PiLp.continuous_toLp _ _ |>.comp (continuous_pi (fun j=> by fun_prop))).continuousAt) hy
  exact he.congr' (by filter_upwards [eventually_gt_atTop m] with n hn; rw [hv _ hn]; rfl)
set_option maxHeartbeats 300000 in
lemma tangent_station (hf:SizeFloor A.clock.kernel.penalty A): ∃ y,Tendsto (fun n=>fderiv ℝ (kin.stationary n m p F) 0) atTop (𝓝 y) := by
  let c:= A.S.side m p; let E:=fieldDir G c 1; let T:= AxisChart G F
  let b₁:= Module.finBasis ℝ E; let b₂ := Module.finBasis ℝ T
  let choice (n:ℕ) := fderiv ℝ (kin.stationary n m p F) 0
  choose v hv using fun j=>tangent_vector M hP kin h hG p m hL hS F hf (b₁ j)
  let f := Matrix.of fun i j=> b₂.equivFun (v j) i
  let H := (LinearMap.toContinuousLinearMap (E:=E) (F':=T)).symm.trans (LinearMap.toMatrix b₁ b₂)
  have ht : Tendsto (H ∘ choice) atTop (𝓝 f):= by
     apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
     dsimp [comp_def, H,f,choice]
     change Tendsto (fun n=> (LinearMap.toMatrix b₁ b₂ (choice n).toLinearMap) i j) _ _
     simp_rw [LinearMap.toMatrix_apply']
     exact ContinuousAt.tendsto ((continuous_apply i).comp b₂.equivFun.toLinearMap.continuous_of_finiteDimensional).continuousAt |>.comp (hv j)
  exact ⟨H.symm f,show Tendsto _ _ _ from by simpa [comp_def,choice] using H.symm.toLinearMap.continuous_of_finiteDimensional.continuousAt|>.tendsto |>.comp ht⟩
end horizon
open PhysicalNext.Repeat.Legato
lemma actual_tangent (X:UVBuild G) (hs:X.Shared) (g:G.Simple) (p m:ℕ) (F:Forest (X.tower.a.clock.op m p).ratio) (hB:SizeFloor X.tower.a.clock.kernel.penalty X.tower.a) :
       ∃ y,Tendsto (fun n=>fderiv ℝ (X.tower.kin.stationary n m p F) 0) atTop (𝓝 y) := by
  obtain ⟨-,-,-,-,-,K,-⟩:=hs.same.reception
  have hx : Bid.Larger (G:=G) (X.tower.a.clock.op m p):= K.sized m p
  exact tangent_station _ X.tower.plan _ X.tower.support g p m hx (fun n hn=> X.works.pledging.conducts.full _ _ _ hn) F hB

end YM.Extension.UV.Linear

import YM.Next.FREE_KERNELS.Amend
import YM.Next.FREE_KERNELS.Sell

/-!
# C₃ positive factor

Use the refined L⁻³ *per residue* payment on the right Laurent lift to
absorb the whole fine contribution. Thus we can pay positive on the entire
three-form coordinates already, not only range `d₂`; no selecting a left
kernel with range depending on the real p. L threshold and previous B₀ cost
make this work even on successive within-stage repetitions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ}
namespace Flight

def render (k m l : ℝ) (P : Flight j t) :=
    minusRows (plusRows (P.fund k) (scaleRows l (unitRow (TypeFace 3))))
      (scaleRows m (net (P.sale k) (P.sale k)))

def rollFunds (k m l : ℝ) (P : Flight j t) :=
    let D := treble k l P.land
    composeRows (composeRows (transRows D) (render k m l P)) D

variable (K : KernelChoices) (m l : ℝ) (hl : 0≤l) (hm : 0≤m) (hj : 4≤j) (ht : 4≤t)

include hj ht
lemma netted : Stock (fee (t:=t) (j:=j) 2) (α:=fun _ => TypeFace 3) (β:=fun _ => TypeFace 3)
    (fun P : Flight j t => net (P.sale K.penalty) (P.sale K.penalty)) := by
  have hh := budget_sale K.penalty K.penalty_pos hj ht
  let B := (Fintype.card (TypeFace 3):ℝ)
  refine (hh.flipped.prod hh).raise (c:=B+1) (by unfold B; positivity) (fun P => ?_)
  change (Fintype.card (Co P.L (TypeFace 3)):ℝ) * _ ≤ _
  unfold fee Co B
  rw [Fintype.card_prod,site_card]; have h := side_pos P.L; push_cast; field_simp; nlinarith
lemma render_stock : Guide (render (j:=j) (t:=t) K.penalty m l) := by
  let S := fun P : Flight j t => P.sale K.penalty
  have hh : Guide (fun P : Flight j t => net (S P) (S P)) :=
    (netted K hj ht).raise (c:=1) one_pos fun P => by
      have h : 1 ≤ (P.L.val:ℝ) := by exact_mod_cast P.L.property
      rw [one_mul]; exact inv_le_one_of_one_le₀ (one_le_pow₀ h)
  have hx := funded K.penalty K.penalty_pos hj ht
  exact (hx.plus ((Stock.constant _ (Whole.coin (TypeFace 3))).weight l)).minus (hh.weight m)

include hl in
lemma roll_stock : Guide (rollFunds (j:=j) (t:=t) K.penalty m l) := by
  have hh := (insurance K.penalty l K.penalty_pos hl ht (fun P : Flight j t => P.land)).2.stock
  have hb := (hh.flipped.times (render_stock K m l hj ht)).times hh; simp only [one_mul] at hb; exact hb

/-- `C` a threshold for *output* amendment coefficient, `B` a cost
for *input* amendment, both ONLY j,t,K. -/
lemma absorb_before : ∃ C B : ℝ, 0<C ∧ 0<B ∧ ∀ (l m : ℝ), 0 ≤ m → C ≤ l →
    ∀ (P : Flight j t), m*B ≤ (P.L.val:ℝ)^2 → ∀ p : Momentum, physical p →
      IsHermitian ((render K.penalty m l P).read p) ∧ ∀ x,
        sqLength x ≤ pairingRe ((render K.penalty m l P).read p) x x := by
  let k := K.penalty
  obtain ⟨η,C,he,hC,h⟩ := (funded k K.penalty_pos hj ht).uniform
  obtain ⟨σ,B,hσ,hB,g⟩ := (netted K hj ht).uniform
  let a := countCeil (TypeFace 3); have ha : 0<a := Work.F06.countCeil_pos _
  refine ⟨a^2*C+2,a^2*B,by positivity,by positivity,fun l m hm hl P hL p hp => ?_⟩
  let U := render k m l P
  let V := P.fund k; let T := net (P.sale k) (P.sale k)
  have hh₁ := (funded k K.penalty_pos hj ht).whole P
  have hS := (budget_sale k K.penalty_pos hj ht).whole P
  have hh₂ := hS.flipped.prod hS
  have hh₃ := Whole.coin (TypeFace 3)
  have hx : U.read p=V.read p+(l:ℂ) • 1 - (m:ℂ) • T.read p := by
    unfold U render net; rw [read_less (hh₁.plus (hh₃.weight _)).safe (hh₂.weight _).safe hp,
      hh₁.read_plus (hh₃.weight _) hp,read_weight,read_weight,read_unit]; rfl
  change IsHermitian (U.read p) ∧ _
  constructor
  · have ht : IsHermitian (V.read p) := (fund_sym ht P K).2 p hp
    have hh : (T.read p)ᴴ=T.read p := by unfold T net; rw [hS.flipped.read hS hp,read_opposite _ hp,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    unfold IsHermitian; rw [hx,conjTranspose_sub,conjTranspose_add,conjTranspose_smul,conjTranspose_smul,ht,hh]; simp
  intro x
  have hb : -(a^2*C*sqLength x) ≤ pairingRe (V.read p) x x := by
    apply (abs_le.mp (Work.F06.pairingRe_diag (V.read p) hC.le _ x)).1
    intro i j; exact (Work.F06.row_entry_le (h P) he.le p hp i j).trans_eq (mul_one C)
  let L := (P.L.val:ℝ)
  have hL' : 0 < L := side_pos P.L
  have hy : pairingRe (T.read p) x x ≤ a^2*(B/P.L.val^2)*sqLength x := by
    have hv i j := Work.F06.row_entry_le (g P) hσ.le p hp i j
    exact (le_abs_self _).trans (Work.F06.pairingRe_diag _ (by positivity) (by unfold T; simpa only [div_eq_mul_inv,fee] using hv) x)
  have hu := Work.F06.sqLength_nonneg x
  have hz : m * pairingRe (T.read p) x x ≤ sqLength x := calc
    _ ≤ m * (a^2*(B/L^2)*sqLength x) := mul_le_mul_of_nonneg_left hy hm
    _ = (m*(a^2*B)/L^2)*sqLength x := by ring
    _ ≤ _ := mul_le_of_le_one_left hu ((div_le_one (pow_pos hL' _)).mpr hL)
  change sqLength x ≤ pairingRe (U.read p) x x; rw [hx,Work.F06.pairingRe_sub,Work.F06.pairingRe_add,Work.F06.pairingRe_scale,Work.F06.pairingRe_scale,price_unit]; linarith [mul_le_mul_of_nonneg_right hl hu]

/-- Separation controls the THREE-form concept here, and the strip
already works at all L. Reaches only asks part of this. -/
lemma frontier : ∃ C B : ℝ, 0<C ∧ 0<B ∧ ∀ (l m : ℝ), 0≤m → C≤l → ∃ η σ D : ℝ,
    0<η ∧ 0<σ ∧ 0<D ∧ ∀ P : Flight j t, (rollFunds K.penalty m l P).strip σ D ∧
    (m*B ≤ (P.L.val:ℝ)^2 → Funds (rollFunds K.penalty m l P) η D) := by
  obtain ⟨C,B,hC,hB,H⟩ := absorb_before K hj ht
  refine ⟨C,B,hC,hB, fun l m hm hl' => ?_⟩
  let k := K.penalty; have hl : 0≤l := hC.le.trans hl'
  obtain ⟨σ,U,hσ,hU,h⟩ := (roll_stock K m l hl hj ht).uniform
  have hu := render_stock K m l hj ht
  let f := fun P : Flight j t => bail k l P.land
  have hf : Warm f := bail_warm k l K.penalty_pos hl ht (fun P : Flight j t => P.land)
  obtain ⟨hy,Hf⟩ := heated hf
  obtain ⟨θ,G,hθ,hG,H₀⟩ := hf.stock.uniform
  let b := countCeil (TypeFace 3); have hb := Work.F06.countCeil_pos (TypeFace 3)
  let D := (Fintype.card (TypeFace 3):ℝ)
  have hD : 0≤D := by unfold D; positivity
  let W := D*(D*G)^2+1; have hW : 0<W := by unfold W; positivity
  let Y := max U (b^2*U)
  refine ⟨W⁻¹,σ,Y,inv_pos.mpr hW,hσ,lt_max_of_lt_left hU,fun P => ⟨?_,fun he p hp => ?_⟩⟩
  · exact strip_mono (h P) le_rfl ((mul_one _).trans_le (le_max_left ..))
  let A := render k m l P
  let F := treble k l P.land
  let R := rollFunds k m l P
  obtain ⟨hh,hx⟩ := H _ _ hm hl' P he p hp
  have hF : Whole F := hy.stock.whole P
  have hA : Whole A := hu.whole P
  have hR : R.read p=(F.read p)ᴴ*A.read p*F.read p := by unfold R rollFunds; rw [(hF.flipped.prod hA).read hF hp,hF.flipped.read hA hp,read_opposite _ hp]
  change IsHermitian (R.read p) ∧ ∀ x, _ ≤ _ ∧ _ ≤ _
  refine ⟨by rw [hR]; exact cross_chart _ hh _, fun x => ⟨?_,?_⟩⟩
  · have hE := hf.stock.whole P
    have hM : composeRows F (f P) = unitRow _ := by
      apply bank_injective (hF.prod hE).safe (Whole.coin _).safe
      intro n; rw [hF.acts hE,acts_unit]; exact (Hf P).2 n
    have hN : F.read p * (f P).read p = 1 := by rw [← hF.read hE hp,hM,read_unit]
    let z := F.read p *ᵥ x
    have hhx : x=(f P).read p*ᵥ z := by unfold z; rw [mulVec_mulVec,mul_eq_one_comm.mp hN,Matrix.one_mulVec]
    have hS : sqLength x ≤ W*sqLength z := calc
      _ ≤ D*(D*G)^2*sqLength z := (congr_arg sqLength hhx).trans_le (growth_price ((f P).read p) hG.le (fun i j => (Work.F06.row_entry_le (H₀ P) hθ.le p hp i j).trans_eq (mul_one _)) z)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold W; linarith) (Work.F06.sqLength_nonneg _)
    change W⁻¹ * sqLength x ≤ pairingRe (R.read p) x x
    rw [hR,paid_through]
    exact ((mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hW.le)).trans_eq (inv_mul_cancel_left₀ hW.ne' _)).trans (hx z)
  apply le_trans (le_abs_self (pairingRe (R.read p) x x)); exact (Work.F06.pairingRe_diag _ hU.le (fun i j => (Work.F06.row_entry_le (h P) hσ.le p hp i j).trans_eq (mul_one _)) x).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Work.F06.sqLength_nonneg _))

omit hj
include hl hm
lemma rebased {c f : Side} (P : Flight j t) (hc : f.val=c.val*P.L.val) :
    let k := K.penalty; let g := P.visitRatio hc
    let X := pledge k m P.wing; let Y := pledge k l P.land
    let B := amend k l P.land
    let T := installed g (P.duo k).T
    B.acts c*(Y.acts c - T.transpose*X.acts f*T-k⁻¹ • (d 1 c*(d 1 c).transpose))*B.acts c=(d 2 c).transpose*(rollFunds k m l P).acts c*d 2 c := by
  intro k g X Y B T
  let M := B.acts c
  let B' := (blue k P.land).acts c; let b' := (blue k P.wing).acts f
  let D := (treble k l P.land).acts c; let V := (gap k P).acts c
  let F := d 2 f * b'; let R := d 2 c * B'; let s := installed g (sale k P)
  have hh := obligations k m K.penalty_pos hm P.legal P.wing f
  have hq := obligations k l K.penalty_pos hl ht P.land c
  have hy : X.acts f=b'+m • (Fᵀ*F) := hh.2.1.2
  have ht' : Y.acts c=B'+l • (Rᵀ*R) := hq.2.1.2
  have hx : R*M=D*d 2 c := hq.2.2.2.1
  have hM : Mᵀ=M := hq.2.2.2.2.1
  have he : s*R=F*T := by rw [show s*R=s*d 2 c*B' from (Matrix.mul_assoc ..).symm]; exact intake ht P K hc
  let C := fund k P; let J := render k m l P; let L := treble k l P.land
  have hC := (funded k K.penalty_pos P.legal ht).whole P
  have hb : Whole L := (insurance k l K.penalty_pos hl ht (fun i : Flight j t => i.land)).2.stock.whole P
  have hS := (budget_sale k K.penalty_pos P.legal ht).whole P
  have hJ := (render_stock K m l P.legal ht).whole P
  have hV : V=B'-Tᵀ*b'*T-k⁻¹ • (d 1 c*(d 1 c)ᵀ) := gap_physical k K.penalty_pos ht P hc
  have hw : V=Rᵀ*C.acts c*R := banked_dollars ht P K c
  have hU : J.acts c=C.acts c+l • 1 - m • (sᵀ*s) := by
    unfold J render; have hn : Whole (net (P.sale k) (P.sale k)) := hS.flipped.prod hS
    rw [(hC.plus ((Whole.coin _).weight l)).less (hn.weight m), hC.acts_plus ((Whole.coin _).weight l), acts_scale, acts_scale,acts_unit,net_action g hS hS]
  have hu : Y.acts c-Tᵀ*X.acts f*T-k⁻¹ • (d 1 c*(d 1 c)ᵀ)=Rᵀ*J.acts c*R := by
    rw [hU]; -- collect T terms through he
    have hv : Rᵀ*(sᵀ*s)*R=Tᵀ*(Fᵀ*F)*T := calc
      _ = (s*R)ᵀ*(s*R) := by rw [transpose_mul s R]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [he,transpose_mul]; simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sub,Matrix.mul_add,Matrix.sub_mul,Matrix.add_mul,← hw,hV,hy,ht']; simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]; rw [hv]; abel
  have ho : (rollFunds k m l P).acts c=Dᵀ*J.acts c*D := by unfold rollFunds; rw [(hb.flipped.prod hJ).acts hb,hb.flipped.acts hJ,acts_trans]
  rw [hu,ho];
  calc M*(Rᵀ*J.acts c*R)*M=(R*M)ᵀ*J.acts c*(R*M) := by rw [Matrix.transpose_mul R M,hM]; simp only [Matrix.mul_assoc]
       _ = _ := by rw [hx, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
end Flight
end YM.Next.Free

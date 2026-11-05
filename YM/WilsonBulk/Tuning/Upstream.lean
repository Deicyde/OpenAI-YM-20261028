import YM.WilsonBulk.Tuning.Beginning
import YM.Progress.JOINT_CALENDAR.Germs

/-!
# Genuine TOP. Finite exponent Wilson rescaled exp(g links) chart jets match all
 initialized sectors: θ-independent. No Gaussian other modes pushed at top.
 Keep canonical plaquette paths dictionary. Initial rank0? No upTerm. Scalar part
 of Haar? enters only next conditioning. Mark: not yet here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier FreeResolvent
open PowerSeries (coeff constantCoeff)
variable {c n : Side} {G : Gauge} {B : Bed} {V : Text (Cloth G) 2} {η A C θ : ℝ} {p : Clip}

abbrev Wild (G : Gauge) := Option Axis × Cloth G -- option center or +axis

def hedgerow (G : Gauge) (k : Wild G) : Mark G := ((k.1.map step).getD 0,k.2)
attribute [local instance] Gauge.frobInner

def stampRot (x : Tabletop (Wild G)) (i : Axis) (j : Option Axis) := G.lieExp (priceScreen (fun k:G.ColorIndex=>(j,coord i,k)) x)
def topStub (p : PlaqAxes) (x : Tabletop (Wild G)) := let a:=p.val.1; let b:=p.val.2; stampRot x a none * stampRot x b (some a) * (stampRot x a (some b))⁻¹ * (stampRot x b none)⁻¹

def progressStub (G : Gauge) (x : Tabletop (Wild G)) := ∑ i:PlaqAxes,G.price (topStub i x)
lemma studio (p : PlaqAxes) : ContDiffAt ℝ ω (fun z : Tabletop (Wild G)=> G.mat (topStub p z)) 0 := by
  let r (j:Option Axis): Tabletop (Wild G)→Axis→G.El:= fun z i=> stampRot z i j
  have hr j : Army (r j) 0 := fun i=> let E:= priceScreen (α:=Wild G) (fun k:G.ColorIndex=>(j,coord i,k)); G.exp_jet.contDiffAt.comp (f:=E) _ E.contDiff.contDiffAt
  let a:=p.val.1; let b:=p.val.2; exact (((hr none a).mul (hr (some a) b)).mul ((hr (some b)).inv a)).mul ((hr none).inv b)
lemma progressJet (G : Gauge) : ContDiffAt ℝ ω (progressStub G) 0 := ContDiffAt.sum (fun i _=> Work.F03.price_smooth (studio i))
-- no nonce: only center/north ⊕ legacy faces
lemma stampNone (x : Tabletop (Co c (Cloth G))) (z : Site c) (i : Axis) : stampRot (socket (ladder (hedgerow G) z) x) i none= signal G c x (z,i) := by
  rw [stampRot,signal_at]; congr 1; ext j; rw [traces_at]; change x (rolls z _ (small _ _ (hedgerow G (none,coord i,j))))=_; simp only [rolls_apply,small,hedgerow,Option.map,Option.getD,map_zero,zero_add]; rfl
lemma stampFall (x : Tabletop (Co c (Cloth G))) (z : Site c) (i j : Axis) : stampRot (socket (ladder (hedgerow G) z) x) i (some j)= signal G c x (z+step j,i) := by
  rw [stampRot,signal_at]; congr 1; ext k; rw [traces_at]; change x (rolls z _ (small _ _ (hedgerow G (some j,coord i,k))))=_; simp only [rolls_apply,small,hedgerow,Option.map,Option.getD,wrap_step]; rw [add_comm]; rfl
lemma topSquare (V : Config G n) (y : Site n) (p : PlaqAxes) :
    let a:=p.val.1; let b:=p.val.2; V (y,a)*V (y+step a,b)*(V (y+step b,a))⁻¹ *(V (y,b))⁻¹=faceValue V (y,p) := by
  intro a b; rcases p with ⟨⟨p,q⟩,h⟩; simp only [a,b,faceValue,Lattice.square,Lattice.travel, Step.read, Step.used, Step.vec,posDir, negDir]; simp; rw [show y+step p+step q-step p=y+step q from by abel]; group
abbrev energyStub (G : Gauge) (c : Side) := energy ∘ signal G c
lemma sector_eq (G : Gauge) (c : Side) : plantSector (hedgerow G) (progressStub G) c= energyStub G c := by
  ext1 x; simp only [plantSector,Function.comp_apply,progressStub, Finset.sum_apply,energyStub,Wilson.energy,Fintype.sum_prod_type,topStub,stampNone,stampFall]; exact Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun i _=> congr_arg G.price (topSquare (signal _ _ x) j i)
lemma luminous (G : Gauge) (c : Side) : ContDiffAt ℝ ω (energyStub G c) 0 := by rw [← sector_eq]; exact cont_diff_sum _ _ (fun i _=> let V:=socket (ladder (hedgerow G) i); (show ContDiffAt ℝ ω _ (V 0) from V.map_zero.symm ▸ progressJet G).comp _ V.contDiff.contDiffAt)

-- complete rescaled sum & engine. Top rule pays far frame powers only post-L.
def upstream (G : Gauge) : Library G := chapters 2 (hedgerow G) (progressStub G)
lemma topTape (G : Gauge) (c : Side) : audienceK G c (upstream G)= zoom (zoom (ink (energyStub G c))) := by unfold audienceK upstream; rw [chapters_decal _ _ _ (progressJet _),sector_eq]
lemma top_style (G : Gauge) : Document (upstream G) := chapters_here 2 _ _ le_rfl rfl
lemma top_public (G : Gauge) : Pamphlet (upstream G) := chaptersPublic 2 _ _
lemma top_free_stmt (G : Gauge) : Cashless (upstream G) := fun i=> by rw [upstream,chapters,if_neg (by omega)]
lemma fiscal (G : Gauge) (c : Side) (B : Bed) (x : Tabletop (Pennant G c)) : MvPolynomial.eval x (forceQ (matrixK G c B) MvPolynomial.X)=Bid.gaugeFiscal B (traces G c 1 x) (traces G c 1 x)/2 := by
  change MvPolynomial.aeval x _=_; rw [forceQ_map _ _ (MvPolynomial.aeval x)]; simp_rw [MvPolynomial.aeval_X]; unfold forceQ furrow; rw [smul_eq_mul,quill_real,matrixK,match_tensor]; change _ * dotProduct _ _ = _; rw [component_dot]; simp_rw [component_mul]; change (1/2:ℝ)*Bid.gaugeFiscal B (traces G c 1 x) (traces G c 1 x)= _; ring
lemma upstream_flag (p : Clip) (G : Gauge) (c : Side) (B : Bed) (hp : Floor B p c η C) (ht : B.diagonal.acts c=1) : PowerSeries.X^2 * audienceK G c (upstream G)=ink (energyStub G c) ∧ constantCoeff (audienceK G c (upstream G))=constantCoeff (grains (matrixK G c B)) := by
  let f:= energyStub G c; have hh (x : Tabletop (Pennant G c)) : Tendsto (fun t:ℝ=> f (t • x)/t^2) (𝓝[≠] 0) (𝓝 (MvPolynomial.eval x (forceQ (matrixK G c B) MvPolynomial.X))) := by
    rw [fiscal]; have hh := Progress.Joint.energy_limit B (traces G c 1 x) hp ht; simp only [f,energyStub,Function.comp_apply, signal,map_smul]; exact hh
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩:= ink_floor (luminous G c) _ hh
  rw [topTape, grains_root]; refine ⟨?_,?_⟩
  · rw [pow_two,mul_assoc,zoom_key,zoom_key]; · exact ink_root h₁
    rw [zoom_const]; exact h₄
  rw [zoom_const,zoom_power,PowerSeries.constantCoeff_C]; exact h₅
end YM.WilsonBulk.Parapet

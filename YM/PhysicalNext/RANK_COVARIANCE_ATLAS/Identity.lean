import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas
import YM.Push.FREE_RESOLVENT.GaugeProjection


/-!
# One conditional covariance in real links

Actual comparison P vs flat conditional. Input one retained unmasked metric
and tower, from the history where Rank analytically calls them. Don't use
a hypothesis that the precision is invertible in a special alias sector;
prove the formula EVEN at harmonic via the real restricted inverse and
oblique tree gauge. No assumption about nonlinear cut kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free
open Further.FreeCovariance.KP
open Further.CorrectedLift.Resolve
open RG FreeResolvent Tree Bid
open Next.Rank Next.Rank.Atlas
open scoped Topology BigOperators ComplexConjugate

section schur
variable {α β ι ν : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype ν]

/-- The core algebra. P,R have image inside cochain-curl image and are inverse
there in the tested sense. Q is the rooted probe and E the response column in
that tree. M,J unmasked metric, I the uncut tree covariance. D,C exact
exterior derivatives. No inverses on null space. -/
private lemma schur (P M : Matrix α α ℝ) (R J : Matrix β β ℝ) (I : Matrix ι ι ℝ)
    (D : Matrix α ι ℝ) (C : Matrix β ν ℝ) (Q : Matrix ν ι ℝ) (E : Matrix ι ν ℝ) (W : Matrix α β ℝ) (k : ℝ)
    (hp : Pᵀ=P) (hm : Mᵀ=M) (hr : Rᵀ=R) (hj : Jᵀ=J) (hh : Iᵀ=I) (hf : ∃ F, P=D*F) (hg : ∃ G, R=C*G)
    (hP : P*M*D=D) (hR : R*J*C=C) (he : W*C=D*E)
    (hK : Dᵀ*M*D*E=Qᵀ*(Cᵀ*J*C)) (hl : D*I*(Dᵀ*M*D+k • (Qᵀ*Q))=D)
    (hE : (Dᵀ*M*D+k • (Qᵀ*Q))*E=k • Qᵀ) : P-W*R*Wᵀ=D*I*Dᵀ := by
  obtain ⟨F,hf⟩ := hf; obtain ⟨G,hg⟩ := hg
  let X := D*I*Dᵀ + W*R*Wᵀ
  have hX : Xᵀ=X := by simp only [X,Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,hr,hh, Matrix.mul_assoc]
  have ha : Cᵀ*Wᵀ*M*D=Cᵀ*J*C*Q := by
    rw [← Matrix.transpose_mul W C,he]
    have hb := congr_arg Matrix.transpose hK
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hj,hm] at *
    simp only [Matrix.mul_assoc] at *; exact hb
  have hb : Gᵀ*Cᵀ=R := by rw [← Matrix.transpose_mul,← hg,hr]
  have hk : R*Wᵀ*M*D=C*Q := calc
    _ = Gᵀ*(Cᵀ*Wᵀ*M*D) := by rw [← hb]; simp only [Matrix.mul_assoc]
    _ = R*J*C*Q := by rw [ha,← hb]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR]
  have hu : D*I*(k • Qᵀ) = D*E := by rw [← hE,← Matrix.mul_assoc (D*I),hl]
  have hz : X*M*D=D := by
    calc
      _ = D*I*(Dᵀ*M*D) + W*(C*Q) := by rw [← hk]; simp only [X,Matrix.add_mul,Matrix.mul_assoc]
      _ = D*I*(Dᵀ*M*D) + D*I*(k • (Qᵀ*Q)) := by rw [← Matrix.mul_assoc W C Q, he, ← Matrix.smul_mul, ← Matrix.mul_assoc _ _ Q, hu]
      _ = _ := by rw [← Matrix.mul_add,hl]
  have hu : X = D*(I*Dᵀ+ E*(G*Wᵀ)) := by unfold X; rw [hg, Matrix.mul_add]; rw [← Matrix.mul_assoc W C]; rw [he]; simp only [Matrix.mul_assoc]
  have hv : X*M*P=P := by rw [hf,← Matrix.mul_assoc (X*M),hz]
  have hw : P*M*X=X := by rw [hu,← Matrix.mul_assoc (P*M),hP]
  have h : P=X := by
    have he := congr_arg Matrix.transpose hv
    rw [Matrix.transpose_mul,Matrix.transpose_mul,hp,hX,hm,← Matrix.mul_assoc, hw] at he; exact he.symm
  rw [h]; unfold X; abel
end schur

variable {G : Gauge} {A : Levels G} {H : Horizon A} {Z : MapPrices} {l : ℕ → ℕ → ℝ} {N i p : ℕ}
variable (hr : ShapePort A H l) (hH : H.Suffices Z)
local notation "V" => A.S.side

def latticeCurl (G : Gauge) (n : Side) := tensor G (Exterior.d 1 n)
def unmasked (H : Horizon A) (N i p) := tensor G ((H.H N i).metric.acts (A.S.side i p))
def linksK (H : Horizon A) (N i p) := tensor G (Precision.K ((H.H N i).metric.acts (A.S.side i p)))

lemma links_precision : linksK H N i p = (latticeCurl G (V i p))ᵀ*unmasked H N i p*latticeCurl G (V i p) := by
  rw [linksK,Precision.K,promote_prod,promote_prod,← tensor_transpose]; rfl

include hr hH
lemma complete_inverse (hi : i≤N) (p : ℕ) :
    let D := latticeCurl G (V i p)
    let T := complete A N i p
    (∃ X, T=D*X) ∧ T*unmasked H N i p*D=D := by
  intro D T
  have hh := hH.all N i hi (V i p)
  have he := Z.eta_pos (A.clock.J i)
  have hw : T = tensor G (screenP hh he) := congr_arg (tensor G (n:=V i p) (f:=V i p) (r:=2) (s:=2)) (scalar_eq_screen hh he (hr.1 _ _ hi) (A.clock.adm i) A.clock.kernel.penalty_pos)
  rw [hw]; let B := (H.H N i).metric.acts (V i p); let L:=Exterior.d 1 (V i p)
  refine ⟨⟨tensor G (field hh he), promote_prod G L _⟩,?_⟩
  change _ * tensor G B * tensor G L= _
  rw [← promote_prod, ← promote_prod]; refine congr_arg _ ?_
  have hm : Lᵀ*B*screenP hh he=Lᵀ := by rw [screenP]; simp only [← Matrix.mul_assoc]; exact hinge hh he
  have hx := congr_arg Matrix.transpose hm
  rw [Matrix.transpose_mul, Matrix.transpose_mul,balanced,show B.transpose=B from hh.symmetric.1,Matrix.transpose_transpose,← Matrix.mul_assoc] at hx
  exact hx



section tree
local notation "S" => A.clock.op i p
local notation "d" => latticeCurl G

/-- Tree-rooted stationary column (absolute fine links vs coarse links). -/
def stationMap (H : Horizon A) (N i p) (F : Forest (A.clock.op i p).ratio) := tensor G
  (extracted (A.clock.op i p) F (installed (A.clock.op i p).ratio (H.towers N i).A0))

/-- Covariance of uncut inverse in flat real color links including tree zeros
(not a covariance after tags or hard flags). -/
def flat (H : Horizon A) (N i p) (F : Forest (A.clock.op i p).ratio) :=
    FreeResolvent.covariance G (A.clock.op i p) F (H.H N (i+1)).metric

variable (hi : i<N) (F : Forest (A.clock.op i p).ratio)
include hi F
lemma pass_path : passage A N i p*d (V i p)=d (V (i+1) p)*stationMap H N i p F := by
  rw [passage,psi_physical _ _ _ _ H hr hi, stationMap]; unfold latticeCurl; rw [← promote_prod, ← promote_prod]; apply congr_arg
  let W:=H.H N (i+1); let C:=H.H N i; let f:=V (i+1) p; let c:=V i p
  let B:= installed (A.clock.op i p).ratio (H.towers N i).T; let X:= installed (A.clock.op i p).ratio (H.towers N i).A0
  change W.dual_diag.acts f*B*C.diagonal.acts c*Exterior.d 1 c=Exterior.d 1 f*extracted S F X
  have he : W.dual_diag.acts f*W.diagonal.acts f=1 := mul_eq_one_comm.mp (hH.all N (i+1) hi f).diagonalInv
  rw [Matrix.mul_assoc _ _ (Exterior.d 1 c),Matrix.mul_assoc,← Matrix.mul_assoc B,show B * (C.diagonal.acts c)*Exterior.d 1 c=_ from (hH.crossings N i p hi).stays,
    ← Matrix.mul_assoc,← Matrix.mul_assoc,he,Matrix.one_mul]
  unfold extracted; rw [Matrix.mul_add,← Matrix.mul_assoc (Exterior.d 1 f) (Exterior.d 0 f), Exterior.closed,Matrix.zero_mul,add_zero]

omit hr in
lemma trees_station :
    let Q := tensor G (probe S)
    let E := stationMap H N i p F
    let k := A.clock.kernel.penalty
    let T := linksK H N (i+1) p
    T * E= Qᵀ * linksK H N i p ∧ (T+k • (Qᵀ*Q)) * E=k • Qᵀ := by
  intro Q E k T
  let C:= H.H N i; let W:=H.H N (i+1); let B:=H.towers N i
  let f:= V (i+1) p; let c:= V i p
  let X := installed (A.clock.op i p).ratio B.A0; let R := extracted S F X
  have hh := stationed F X (W.metric.acts f) (C.metric.acts c) (hH.crossings N i p hi).trial
  have hy : Q*E=1-k⁻¹ • linksK H N i p := by
    change tensor G (probe S) * tensor G R = _; rw [← promote_prod, hh.1,promote_diff,promote_one,promote_coeff]; rfl
  have ht : T*E=Qᵀ*linksK H N i p := by
    change tensor G (Precision.K (W.metric.acts f))*tensor G R=_; rw [← promote_prod,hh.2,promote_prod,← tensor_transpose]; rfl
  refine ⟨ht,?_⟩; rw [Matrix.add_mul,ht,Matrix.smul_mul,Matrix.mul_assoc,hy, Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one, smul_sub, smul_smul, mul_inv_cancel₀ A.clock.kernel.penalty_pos.ne', one_smul]; abel

variable (hs : Larger (A.clock.op i p) (G:=G))
include hs
omit hr in
lemma recovered :
    let Q:= tensor G (probe S)
    let f:=V (i+1) p
    d f * flat H N i p F * (linksK H N (i+1) p+A.clock.kernel.penalty • (Qᵀ*Q))=d f := by
  intro Q f
  let D := H.H N (i+1)
  have he : fullMatrix G S D.metric=linksK H N (i+1) p + A.clock.kernel.penalty • (Qᵀ*Q):= by
    rw [fullMatrix,baseMatrix,promote_sum,promote_coeff,promote_prod,← tensor_transpose]; rfl
  let a := Z.η (A.clock.J (i+1)); have ha : Gap (D.metric.acts f) a:= ⟨fun x => ((hH.all N (i+1) hi f).uniform.1 x).1⟩
  have ht (x : Vec G f 0) : d f *ᵥ gradient x = 0 := by
    rw [gradient,Matrix.mulVec_mulVec,latticeCurl,← promote_prod,Exterior.closed,promote_zero,Matrix.zero_mulVec]
  rw [← he]; apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [flat,block_solve F D.metric hs (Z.eta_pos _) ha x,representative,Matrix.mulVec_add,ht,add_zero]

-- The mean in the same precision (absolute fine links at scale one,
-- coarse observation Q). Includes the zero extension to tree links. No
-- copied-link subtraction; if using relative coords, that offset must be
-- restored separately.
omit hr in
lemma stationary_mean :
    stationMap H N i p F=flat H N i p F * (A.clock.kernel.penalty • (tensor G (probe S))ᵀ) := by
  have he:= (trees_station hH hi F).2
  let D:= H.H N (i+1)
  let Q:= tensor G (probe S)
  have hp : fullMatrix G S D.metric=linksK H N (i+1) p + A.clock.kernel.penalty • (Qᵀ*Q):= by
    rw [fullMatrix,baseMatrix,promote_sum,promote_coeff,promote_prod,← tensor_transpose]; rfl
  let f:= V (i+1) p; let a:= Z.η (A.clock.J (i+1)); let E:= stationMap H N i p F
  have hD : Gap (D.metric.acts f) a:= ⟨fun x => ((hH.all N (i+1) hi f).uniform.1 x).1⟩
  rw [← he]; change E=_ * ( _ * E)
  rw [← hp]
  apply Matrix.ext_iff_mulVec.mpr; intro x
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, flat,block_solve F D.metric hs (Z.eta_pos _) hD]
  refine (FreeResolvent.fixes F ?_).symm
  intro i; rw [show E=tensor G _ from rfl,component_mul]; exact Precision.stays _ _ _

-- Witness also the gap needed to identify this with a Gaussian covariance.
omit hr in
lemma tree_positive :
    (treeMatrix G S F (H.H N (i+1)).metric).PosDef := by
  let f:=V (i+1) p; let D := H.H N (i+1); let a:= Z.η (A.clock.J (i+1)); let T:=treeMatrix G S F D.metric
  have he:= hH.all N (i+1) hi f
  have hx : Gap (D.metric.acts f) a := ⟨fun x=> (he.uniform.1 x).1⟩
  have hS:= tree_gap S F D.metric hs (Z.eta_pos _) hx
  have ht : Tᵀ = T := by unfold T treeMatrix; rw [Matrix.transpose_submatrix, full_symmetric _ he.symmetric.1]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ht
  intro x hx
  change 0 < star x ⬝ᵥ (T *ᵥ x)
  rw [show star x=x from star_trivial _]; apply lt_of_lt_of_le _ (hS.lower x)
  exact mul_pos (treeFare_pos _ _ _ (Z.eta_pos _)) (dotProduct_star_self_pos_iff.mpr hx)

omit hr in
lemma flat_psd : (flat H N i p F).PosSemidef := by
  have hx := tree_positive hH hi F hs; have hu : (treeInverse G S F (H.H N (i+1)).metric 0).PosSemidef := by
    rw [treeInverse,resolve,zero_smul,add_zero]; exact hx.inv.posSemidef
  exact hu.mul_mul_conjTranspose_same (insertion (plant F))

theorem one_fold :
    let f := V (i+1) p
    let W := passage A N i p
    complete A N (i+1) p - W*complete A N i p*Wᵀ = d f * flat H N i p F * (d f)ᵀ := by
  intro f W; let c:= V i p
  let k := A.clock.kernel.penalty; let Q := tensor G (probe S)
  have ht (j : ℕ) (h : j ≤ N): (unmasked H N j p)ᵀ=unmasked H N j p := by
    rw [unmasked,tensor_transpose, (hH.all N j h (V j p)).symmetric.1]
  obtain ⟨hg,hM⟩ := complete_inverse hr hH (show i+1≤N from hi) p
  obtain ⟨hb,hR⟩ := complete_inverse hr hH (show i≤N from hi.le) p
  obtain ⟨hK,hL⟩:= trees_station hH hi F
  have hx:=recovered hH hi F hs
  simp_rw [links_precision] at hK hL hx
  exact schur _ (unmasked H N (i+1) p) _ (unmasked H N i p) _ (d f) (d c) Q (stationMap H N i p F) W k
    (symmetric_complete ..) (ht (i+1) hi) (symmetric_complete ..) (ht i hi.le)
    (covariance_symmetric _ _ (hH.all _ _ hi f).symmetric.1) hg hb hM hR (pass_path hr hH hi F) hK hx hL


end tree
end YM.PhysicalNext.RankCovariance

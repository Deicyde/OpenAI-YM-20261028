import YM.Next.RANK.Helix
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Identity


/-!
# Into the principal comparison ports

The EXACT equalities are to the uncut flat P_cond and stationary link
lift. `Lead` with short-address requirements won't in general equal this
`track`; neither need a selected V/kernel law on a health test be the
centered flat law! Its closeness on the SAME stamps and branch is a **further
physics input**, not substituting equality for those tests. Tensors below
in link units normalized before leading Gaussian calculation (`anneals` etc).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free
open RG FreeResolvent Tree Bid
open Next.Rank Next.Rank.Atlas Next.Rank.Tapes Normal
open scoped Topology BigOperators ComplexConjugate Classical

section charts
variable {V V' X X' W : Type*} [Fintype V] [Fintype V']
variable (s : X' → V' →₀ ℂ)

private lemma via_reads (x : V' → ℂ) : reads s x=Matrix.of (fun i j=>s i j)*ᵥ x := by
  funext i
  rw [reads,Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=Finset.univ) (by simp)]
  rfl

/-- Convert the scope operation once. `e,g` remember the PAC
permutations. Fin torus reindex SUM; bilinear transpose. -/
private lemma reindex_bill (A : Normal.Symmetric V') (e : X' ≃ X) (g : V' ≃ V) (B : Matrix X V ℝ) (C : Matrix V V ℝ)
    (he : ∀ i j, s i j=↑(B (e i) (g j))) (hC : ∀ i j,A.cov i j=↑(C (g i) (g j))) (i j:X') :
    (scope s A).cov i j=↑((B*C*Bᵀ) (e i) (e j)) := by
  let K := B.submatrix e g; let L:= C.submatrix g g
  have hb : B.submatrix e g * C.submatrix g g=(B*C).submatrix e g := Matrix.submatrix_mul_equiv _ _ e g g
  have ht : K*L*Kᵀ = (B*C*Bᵀ).submatrix e e := by unfold K L; rw [hb]; exact Matrix.submatrix_mul_equiv (B*C) Bᵀ e g e
  change treats A (s i) (s j)=_
  unfold treats
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=Finset.univ) (by simp)]
  rw [show (Finsupp.linearCombination ℂ A.cov (s i))=_ from Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=Finset.univ) (by simp)]
  change _ = (↑(( (B*C*Bᵀ).submatrix e e) i j) : ℂ)
  rw [← ht]
  simp only [Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,he,hC,K,L,Matrix.transpose_apply,Matrix.submatrix_apply]
  apply Finset.sum_congr rfl; intro a _; rw [mul_comm]
end charts

variable {G : Gauge} {n : Side}

def toLinkPAC : linkColor G n ≃ Slot G n 1 :=
    ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _))))

def packLinks (z : linksOn G n) : Vec G n 1 := fun x=> z (x.1,axisEquiv.symm x.2.1) x.2.2
def unpackLinks (z : Vec G n 1) : linksOn G n:= fun x=> WithLp.toLp 2 fun j => z (x.1,axisEquiv x.2,j)

lemma pack_actual (z : Vec G n 1) : packLinks (unpackLinks z) = z := by ext ⟨x,a,j⟩; change z (_,axisEquiv (axisEquiv.symm a),j)=_; rw [Equiv.apply_symm_apply]
lemma corner_price (z : linksOn G n) (i : Incidence G n) :
    froth z i=(latticeCurl G n*ᵥpackLinks z) (toPAC i) := by
  rcases i with ⟨x,b,j⟩
  rw [latticeCurl]
  change froth z (x,b,j)=component (tensor G (Exterior.d 1 n) *ᵥ _) j (x,plaquette b)
  rw [component_mul,d_plaquettes]
  unfold froth rigid rho
  simp only [fromBead,PiLp.sub_apply,PiLp.add_apply,component, packLinks,ix]
  simp only [← coord_map,Equiv.symm_apply_apply]
  abel

lemma stem_table (x : Incidence G n) (y : linkColor G n) :
    stem x y= ↑(latticeCurl G n (toPAC x) (toLinkPAC y)) := by
  let v : linkColor G n → ℝ := Pi.single y 1
  have hx : packLinks (valves v)=Pi.single (toLinkPAC y) 1 := by
    funext z; change v (toLinkPAC.symm z)=_
    simp [v,Pi.single_apply,Equiv.symm_apply_eq]
  have H : (↑(froth (valves v) x) : ℂ)=reads stem (fun i=> (v i:ℂ)) x := by
    rw [reads,stem]; simp only [_root_.map_sub,_root_.map_add,Finsupp.linearCombination_single,one_smul]; unfold froth rigid rho; dsimp only
    rw [PiLp.sub_apply,PiLp.sub_apply,PiLp.add_apply]; push_cast; rfl
  rw [corner_price,hx,via_reads stem] at H
  simpa [v,Pi.single_apply, Matrix.mulVec,dotProduct,mul_ite,apply_ite ((↑) : ℝ → ℂ)] using H.symm

section compare
variable {A : Levels G} {H : Horizon A} {Z : MapPrices} {l : ℕ → ℕ → ℝ} {N i p : ℕ}
variable (hr : ShapePort A H l) (hH : H.Suffices Z) (hi : i<N) (F : Forest (A.clock.op i p).ratio)

/-- Tag covariance in UNcut, flat, real-counting comparison. -/
def flatLinks : Normal.Symmetric (linkColor G (A.S.side (i+1) p)) :=
  toNormal ((flat H N i p F).submatrix toLinkPAC toLinkPAC) (by rw [Matrix.transpose_submatrix,flat,covariance_symmetric _ _ (hH.all N (i+1) hi _).symmetric.1])

/-- Mean lift in the flat tree, on all links not quotient coordinates. -/
def flatColumn (H : Horizon A) (N i p : ℕ) (F : Forest (A.clock.op i p).ratio) :
    linksOn G (A.S.side i p) →ₗ[ℝ] linksOn G (A.S.side (i+1) p) where
  toFun u := unpackLinks ((stationMap H N i p F)*ᵥpackLinks u)
  map_add' a b := by rw [show packLinks (a+b)=packLinks a+packLinks b from rfl, Matrix.mulVec_add]; rfl
  map_smul' c a := by rw [show packLinks (c • a)=c • packLinks a from rfl,Matrix.mulVec_smul]; rfl

include hr hH hi
lemma mean_identity (v : linksOn G (A.S.side i p)) (x : Incidence G (A.S.side (i+1) p)) :
    froth (flatColumn H N i p F v) x =
      Complex.re (Normal.reads ((stamp A N p).path i) (fun j=> (froth v j:ℂ)) x) := by
  simp_rw [via_reads, corner_price]
  let z := stationMap H N i p F *ᵥ packLinks v
  rw [show packLinks (flatColumn H N i p F v)=z from pack_actual _]
  unfold z; rw [Matrix.mulVec_mulVec,← pass_path hr hH hi F,← Matrix.mulVec_mulVec]
  let w:=passage A N i p; let Y := latticeCurl G _ *ᵥ packLinks v
  change w (toPAC x) ⬝ᵥ Y=_
  rw [Matrix.mulVec]; simp only [dotProduct,Matrix.of_apply,path_entry,← Complex.ofReal_mul,Complex.re_sum,Complex.ofReal_re]
  exact (Equiv.sum_comp toPAC (fun i=> w (toPAC x) i * Y i)).symm

omit hr in
lemma tag_entries (x y : Incidence G (A.S.side (i+1) p)) :
    let I:= flat H N i p F
    let L:= latticeCurl G (A.S.side (i+1) p)
    (Normal.scope stem (flatLinks hH hi F)).cov x y = ↑((L*I*Lᵀ) (toPAC x) (toPAC y)) := by
  intro I L; exact reindex_bill stem (flatLinks hH hi F) toPAC toLinkPAC L I stem_table (fun _ _ => rfl) x y

-- PROVES the hReach analytic target's precise comparison
-- matrix, NOT the bound vs selected/truncated uses of different E, R.
lemma principal_match (hs : Larger (A.clock.op i p) (G:=G)) :
    Normal.scope stem (flatLinks hH hi F) = (track (stamp A N p) i).Q := by
  let P:= stamp A N p; let f:=A.S.side (i+1) p; let I:= flat H N i p F; let L:=latticeCurl G f; let B:=flatLinks hH hi F
  let Q:= complete A N (i+1) p; let R:=complete A N i p; let W:=passage A N i p
  apply Normal.Symmetric.ext; funext i' j'
  change (scope stem B).cov _ _=((P.κ (i+1)).cov _ _+ -(scope (P.path i) (P.κ i)).cov _ _)
  rw [show (scope stem B).cov i' j' = _ from tag_entries hH hi F i' j']
  rw [show (scope (P.path i) (P.κ i)).cov i' j' = _ from reindex_bill (P.path i) (P.κ i) toPAC toPAC W R (path_entry A N i p) (fun i j=>rfl) _ _]
  have hx : Q-W*R*Wᵀ=L*I*Lᵀ := one_fold hr hH hi F hs
  change ↑((L*I*Lᵀ) _ _)=(↑(Q _ _):ℂ)+-(↑((W*R*Wᵀ) _ _))
  rw [← hx,Matrix.sub_apply,Complex.ofReal_sub]; abel
end compare
end YM.PhysicalNext.RankCovariance

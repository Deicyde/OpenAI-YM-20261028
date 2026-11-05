import YM.MergeProof.North.Sultan
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d h:ℕ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (x:Cover)(B: C.label d) (T:C.label 4) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (hj:j<N)
local notation "f"=> Next.UVStress.fragment (C:=C) (D:=D) (d:=d) h rad T B j x N p
local notation "τ"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hj.le)))) 0
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
local notation "A"=> whims C j m d h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level 4).coeffSize T ≤ b)
local notation "ℓ"=> wrap (C.side j p) x
local notation "L"=> bites C J j p ℓ
local notation "O"=> Cells.location C.S j N p x
local notation "W'"=> ventola C.path.levels j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "k₀"=> scurry C.path.levels r χ η (m+1)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hj.le)
structure Wares (i₀ D : ℕ) (χ:ℕ→ℝ)(η X:ℕ→ℝ):Prop where
    city : ∃ σ : ℕ→ℝ, Thor C.path δ r μ σ χ i₀
    crisp j : i₀ ≤ j → χ j ≤ 1
    funs i : i₀≤ i→ 0 < η i ∧ η i ≤1
    bars i : i₀ ≤ i → (((Y|>.budget i).B+(Y|>.budget i).B+1 :ℕ):ℝ)^4*scurry C.path.levels r χ (η i) i≤1/2 ∧ Real.exp (scurry C.path.levels r χ (η i) i)-1≤1
    dollars i : i₀ ≤ i→1 ≤ X i
    brings (i): i₀ ≤ i → ∀ N p:ℕ,∀ hi:i<N, MergeProof.Float.Runs (μ N p i hi) (C.path.levels.clock.op i p) (6*((C.S.block i).val:ℝ)) ∧ Throws C.path N p i (μ N p i hi) (Next.Foundations.hol G) (Next.Foundations.localSection G D) (X i)
local notation "B!"=> ((P').B^2+1+2*polls C.path.levels (m+1))
include hh hp hR hB hT
lemma sales (ha:0<a)(hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref 4 ≤ j)(hW:rad/16≤ ‖C.S.place ℓ‖)(hw':‖C.S.place ℓ‖ ≤4*rad)(he:Interior ((τ).chamber 0) (C.O N p T O))(hs:Interior ((τ).chamber 0) (C.O N p B 0))(he':∀ z:C.label D, Interior ((τ).chamber 0) (C.O N p z 0))
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ Y' H')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ: B! ≤ (C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   ∃ z:C.label D,Next.UVStress.quota C D m N p z ≤ 2*e∧ Interior ((τ).chamber 0) (f z) ∧ (τ).rootTest (C.beta N p) (f z) ≤ 2*(stakes C J k / c):=by
   obtain ⟨σ,hZ⟩:=hr.city; let R':ℂ:= (↑(rad):ℂ)^h; let M:= C.O N p B 0; let U:=R' • C.O N p T O
   have hA' z: (f z)=M*U-C.O N p z 0:=by funext i; change R'*(C.O N p T (O) i)*M i-C.O N p (d:=D) z 0 i = M i*(R' *_)- _; ring
   have hΔ := hI.trans m.le_succ; let t:Bool→ℕ:= Bool.rec d 4; let t':Π i:Bool,C.label (t i):= Bool.rec (motive:=fun i=> C.label (t i)) B (R' • T)
   let s:Bool→ Config G (C.side N p)→ℂ:= Bool.rec M U
   have hX (i:Bool): s i= C.O N p (t' i) (L N (0,i)):= by
      cases i
      · rw [biteF,zeroMama C J p N (by omega)]
      rw [biteT C J j p N ℓ (by omega), vect C j p N ℓ hj.le, show (C.S.toDepth hj.le p).embed ℓ= O from by rw [Cells.location,dif_pos hj.le]]
      exact ((C.linearO N p 4 O).mk' _ |>.map_smul R' T).symm
   have hμ(i:Bool): Interior ((τ).chamber 0) (s i):=by cases i; exact hs; exact he.scale _
   have hv(i:Bool): A i * Spindle.paid C (t i) j N p (t' i) ≤ fly C.path.levels (t i) j :=by
      cases i
      · exact paid_new C N p j d hh B a ha hB h' hj
      change plumR C 4 b j/(rad)^h * Spindle.paid C 4 j N p (R' • T) ≤ _; rw [paid_scale C N p j _ hh hp hT' T R' hj.le,show ‖R'‖=(rad)^h from by unfold R';rw [norm_pow,Complex.norm_real, Real.norm_of_nonneg (fugap C m|>.le)],←mul_assoc,div_mul_cancel₀ _ (pow_pos (fugap _ _) _|>.ne')]; exact paid_new C N p j 4 hh T b hb hT hT' hj
   subst X η; obtain ⟨z,hz,hU⟩:= mutation C N m p D J k c A ℓ hf hk hj hm t t' hh hp hI hR r₀ hx hK (Bool.rec (motive:=fun i=> C.ref (t i) ≤ j) h' hT') hv (fundR C j m d h b a ha hb) hR' hΩ hW hw' s (fun i=>by rw [hX i]; exact (itemT C N p _ hh (t' i) (L N (0,i))).symm) (fun i=> by rw [hX i]; exact C.continuousO ..) hμ he' hZ (hr.funs _ hΔ|>.1) (hr.funs _ hΔ|>.2) (hr.brings m hI N p _|>.2) (hr.dollars m hI) (hr.crisp j (by omega)) (fun i he hi=>hr.brings i (by omega) N p (hi.trans hj)|>.1) (hr.bars _ hΔ|>.1) (hr.bars _ hΔ|>.2) hw hL hV hA hC
   refine ⟨z,hz,?_⟩; rw [hA' z] -- target exists not yet
   exact ⟨Next.UVStress.minus ((hμ false).times (hμ true)) (he' _),hU⟩
end
end YM.MergeProof.Ribbons

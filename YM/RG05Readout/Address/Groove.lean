import YM.RG05Readout.Address.Bend
import YM.RG05Readout.Address.Lit
/-!
# Stencil heading -- each low test-native slot

Include field-only upward rows with no PPX smallness request. Diagonal model
here refers only to those on/above its cost curve; does not claim prediction
on the rest. Prices certified before selecting the stencil v on each step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
variable {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α c β a:ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
variable (k:Letter d)(o:Site (C.side (m+1) p)) (j:(C.labels.level (kept k)).Index) {T:Heading (C.labels.level (kept k))}
local notation "W"=> F (kept k)
variable (ho:(C.path.levels.clock.op m p).ratio.parent o=0) (hw: Pricing (C.localSection (kept k)) C.path N p m C.params D T a c α β)
-- factors totaled in signed schedule

def stCost (d:ℕ)(K:ℝ):ℝ:=K*(K+(2*K+1))+(Fintype.card (Letter d):ℝ)*K^2*(2*K+1)
def aCost (d:ℕ)(K:ℝ):ℝ:=K+(Fintype.card (Letter d):ℝ)*K^3
local notation "Ct"=> (Fintype.card (Letter d):ℝ)
def oldCost (d:ℕ)(K:ℝ):ℝ:= 1+(Fintype.card (Letter d):ℝ)*K^3

def leadScale (C:Family G) (O:Side) {d:ℕ}(i:Mark C d)(T:Heading (C.labels.level (kept i.1))):Palette C d:=
    chunk i.1 (T.leads O (Size.axis (C.labels.level (kept i.1)) i.2))
def micro (C:Family G) {d:ℕ} {n:Side} (b:Mark C d) (o:Site n)(J:Rep G n):=glyph (readJ b.1 0) (invoice (Extra.Histories.primary o (Size.axis (C.labels.level (kept b.1)) b.2)) o (C.localSection (kept b.1)) J)
include hp h hm hδ ho hw
lemma primary_curve (hc:1≤c)(hα:0≤α)(hβ:0≤β) : let b:Mark C d:=⟨k,j⟩; let u:= c*chargeN L b
     let H:= (micro C b o M).comp (Native.pull δ ℓ)
     ∃ V:Tape G (C.side m p),∃ x z:Palette C d, Course (D:=D) o H V x z (stCost d K*u) (aCost d K*(1+u+β+K*u)) ∧ size x≤aCost d K*u ∧ size (Address.clear C d (weights b) (x-leadScale C L b T)) ≤ oldCost d K*α:=by
   intro b u H; let X':= Size.axis W j; let P:=(Extra.Histories.primary o X'); let y:=invoice P o (S (kept k)) M; have ht:0≤K:=(zero_le_one.trans hp.fits)
   obtain ⟨Q,hP,hR,hY,hU,hV⟩:= primary_grant C N m p (kept k) o D h hm ho hw j hα hc hβ -- i infer?
   let r:=((W).grades j).1
   have hz(v': (W).Coeff)(hk:ℕ)(hf:hk≤r): basisCut W hk v'=basisCut W hk ((basisCut W r) v'):=funext fun i=>by
       by_cases hZ:((W).grades i).1≤hk
       · simp [basisCut,hZ,hZ.trans hf]
       simp [basisCut,hZ]
   have hF : (W).coeffSize (vowel W L (Size.axis W j))=chargeN L b:=by
       rw [scale_n]; unfold chargeN b weights; simp only [kept,Nat.sub_sub]
   rw [hF] at hU hR hY
   let T':= T.leads L X'
   have hx(h₁:ℕ)(h₂:h₁<r): basisCut W h₁ T'=0:=by
       let w:ℂ:= ↑(chargeN L b)
       have he : vowel W L X'=w • X':=by
           funext i; by_cases hj:i=j
           · subst i; unfold X' vowel w chargeN b Size.axis weights kept; rw [Nat.sub_sub];push_cast;rfl
           unfold X' vowel Size.axis; simp [hj]
       have hA:= congr_arg T.map he; rw [map_smul] at hA; change T'=_ at hA; rw [hA,map_smul]; suffices hQ : basisCut W h₁ (T.map X')=0 by rw [hQ,smul_zero]
       funext i; unfold basisCut; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
       by_cases hh: ((W).grades i).1≤h₁
       · rw [if_pos hh]; by_contra hv
         have htV:= hw.lower.triangular i j (by rintro hX; subst i; exact (not_le_of_gt h₂) hh) hv; exact (Nat.not_le_of_gt htV) (hh.trans h₂.le)
       rw [if_neg hh];rfl
   have hh(k':ℕ)(hk:k'<r) : (W).coeffSize (basisCut W k' Q.x)≤α:=by
       have ho : basisCut W k' (Q.x-T')=basisCut W k' Q.x:=by rw [map_sub,hx k' hk,sub_zero]
       rw [← ho,hz (Q.x-T') k' hk.le]; exact (cap_rows ..).trans hV
   obtain ⟨V,x,z,hC,hA,hz'⟩:= primitive hp h hm hw.soundD hδ k r Q y o hP hR hY hh hα
   let e:=(W).coeffSize Q.x; refine ⟨V,x,z,⟨hC.paid.grow ?_,hC.ready.extend ?_⟩,?_,?_⟩
   · calc K*(K*e+(2*K*e+u))+Ct*K^2*(2*K*e+u) ≤ K*(K*u+(2*K*u+u))+Ct*K^2*(2*K*u+u):=by gcongr
          _=_:=by unfold stCost;ring
   · change (aCost d K)*(1+u+β+K*e) ≤ _; unfold aCost; gcongr
   · have hu:0 ≤ u:=by unfold u; exact mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans (charge_one ..))
     exact (hA.trans (mul_le_mul_of_nonneg_left hU (by positivity))).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht) hu)
   let n:=depth k+r; let D':=Address.clear C d n
   have ht : D' (chunk k Q.x-leadScale C L b T)=chunk k (basisCut W r (Q.x-T')):=by
      have hw : chunk k Q.x-chunk k T'=chunk k (Q.x-T'):=by
         ext1 i; by_cases hi:i=k
         · subst i; simp
         simp [hi]
      change D' (chunk k Q.x-chunk k T')=_; rw [hw,cpart]; unfold n; rw [if_pos (Nat.le_add_right ..),Nat.add_sub_cancel_left]
   change size (D' _) ≤ _; rw [show x-leadScale C L b T=(x-chunk k Q.x)+(chunk k Q.x-leadScale C L b T) from by abel,map_add,ht]
   apply (size_add ..).trans; rw [size_chunk]
   exact (add_le_add hz' hV).trans_eq (by unfold oldCost;ring)
end YM.RG05Readout.Address

import YM.MergeProof.Buys
import YM.MergeProof.Close
import YM.MultiNext.VACUUM_STABILITY.Localized.Cascade

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open Local Extra.Trajectories Source Extra.Multi
variable [Fintype V] (A: Rep G n) {B:Census V}
    {Φ:V→ Config G n→ℂ}{k:V→ ℕ→ Config G n→ℂ}
variable {t c e d δ v : ℝ} {o:V→ Site n}
variable (ψ:V→MergeProof.Response G n) {w:V→ℝ}
variable (K:Box n→ Config G n→Poly B)(F:Config G n→Poly B)
    (hs:Garnish A.p o ψ w e c)(hv: ∀ i, Flow o i (K i) A.p.threshold)
    (h:∀ i U,(K i U).part B.quiet=profile A.activities (fun j=>Complex.ofReal ∘ A.activities.K j) i U)
    (hr:A.activities.Valid A.p δ v)
local notation "κ"=> closure K (conviction ψ B) Prod.snd A.p.threshold
local notation "J'"=> kelp ψ B
variable {W S C μ a z u : ℝ}
local notation "T0"=> A.p.threshold
local notation "R0"=> A.p.B
-- exact existence after projection, independently Pareto bounds n. Need F+ci.. Setting d<E, etc by user.
include h hr hs hv
lemma curtainC {M:ℕ}{H:Support n→ Config G n→Poly B}
    (h0:∀ x,(F x).part B.quiet=0)(hH:∀ U (p:B.Mode), 2 ≤ p.val.card → (F U).part p=(∑ i,H i U).part p)
    (hw:∀ i,0<w i)(hu:0≤ c)(hh:Occupancy o M)(hY:∀ p,Burns o p (H p) A.p.threshold)(hE:Towed w id H A.p.B (d+μ) S)(hK:Towed w Prod.fst K A.p.B e W)
    (hq:e=d+μ+z)(hf:0 ≤ d+μ) (hp:((A.p.B + A.p.B +1:ℕ):ℝ)^4*(W+M*siteFactor A.p.B*c)≤z)
    {w':V→ℝ}(hw':∀ i,0<w' i)(hg:Repegs o A.p.B w w' μ a B)(ha:0≤a)(hc:a*S ≤ C)(hc':a*(Real.exp (W+M*siteFactor A.p.B*c)-1) ≤ C)
    (hZ:∀ i j U,(K i U).part (B.fire j)+hook A.activities A.p.threshold (ψ j) i U=profile A.activities (k j) i U)
    (ht:∀ i U,(play A B K F U).part (B.fire i)=coin A (Φ i) (k i) U)(hy:∀ i,Dominated (k i))(hit:∀ U,A.eval U≠0): let Z i U:= octave (κ i U); let Y i U:= octave (H i U); Carton o Y Z A.p.threshold ∧ Towed w' id Y R0 d C ∧ Towed w' Prod.fst Z R0 d C ∧ play A B K F=restore A Φ (fun i=>profile A.activities (k i)) Y Z:=by
   let U₀:=conviction ψ B
   have hF(i):=threshed K U₀ Prod.snd T0 hv (dresses ψ B hs) i
   have hB : Towed w Prod.fst κ R0 (d+μ) (Real.exp (W+M*siteFactor A.p.B*c)-1) := branch K U₀ Prod.snd (A.p.threshold) w (hq ▸ hK) (hq ▸ stock ψ B hs hw hh hu) hw hf hp
   have hu:play A B K F=play A B κ (F-J'):=funext fun U=>reversal A ψ K F hs hv U (h0 U)
   obtain ⟨he,hv⟩:=plank A B κ (F-J') Φ k hr (H:=H) (o:=o) (fun i U=> (wine K U₀ Prod.snd T0 _ i (fun p=>hv p|>.permits U) (corn_quiet ψ B U)).trans (h i U)) (fun U=>(by simp only [Pi.sub_apply,part_sub,kelp,Poly.part_sum,h0,corn_quiet ψ B,sum_const_zero,sub_zero])) hY hF hy (fun i U j=>(posts A ψ K hv h hr U i j).trans (hZ ..)) (fun i U=> hu ▸ ht i U) hit (fun U p hp=> by simp only [Pi.sub_apply,part_sub,kelp,corn_light ψ p hp U,sub_zero,hH U p hp])
   · intro Z Y; refine ⟨he,?_,?_,hu.trans hv⟩
     · exact ((hE.sift.peg (fun i=> (he.exp i).1.toBorne) (fun i=>(he.exp i).2) hg hw hw' ha)).shrink le_rfl hc hw'
     exact ((hB.sift.peg (fun i=> (he.flag i).1.toBorne) (fun i=>(he.flag i).2) hg hw hw' ha)).shrink le_rfl hc' hw'
end YM.MergeProof.Accent

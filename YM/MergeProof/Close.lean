import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.MergeProof.Garnish
import YM.MergeProof.Hens
import YM.MergeProof.Sigil
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open Local Extra.Trajectories Source Extra.Multi
variable [Fintype V] (A: Rep G n) {B:Census V}
    {Φ:V→Config G n→ℂ}{k:V→ ℕ→Config G n→ℂ}
variable {t c e d δ v : ℝ} {o:V→ Site n}
variable (ψ:V→MergeProof.Response G n) {w:V→ℝ}
omit [Fintype V] in
lemma corn_quiet (B:Census V)(U:Config G n) (i) : (conviction ψ B i U).part B.quiet=0:=by unfold conviction; simp [(B.fire_hot i.fst).symm]
lemma corn_light (i:B.Mode)(h:2 ≤ i.val.card)(U:Config G n) : (∑ j, conviction ψ B j U).part i=0:=by
   rw [Poly.part_sum]; refine sum_eq_zero fun j _=>?_ ; have he:i ≠ B.fire j.1:=fun e=> by rw [e] at h; simp [Census.fire] at h
   unfold conviction; simp [he]

variable (K:Box n→Config G n→Poly B)(F:Config G n→Poly B)
    (hs:Garnish A.p o ψ w e c)(hv: ∀ i, Flow o i (K i) A.p.threshold)
    (h:∀ i U,(K i U).part B.quiet=profile A.activities (fun j=>Complex.ofReal ∘ A.activities.K j) i U)
    (hr:A.activities.Valid A.p δ v)
local notation "κ"=> closure K (conviction ψ B) Prod.snd A.p.threshold
local notation "J'"=> kelp ψ B
include hs hv
lemma arranged (U:Config G n) : field (fun i=> κ i U) (flags A.p.threshold U)=field (fun i=>K i U) (flags A.p.threshold U)* Poly.pass (J' U):=by
   rw [allclosed,kelp]; exact congr_arg (_*·) (pass_sum (R:=B) Finset.univ (fun i:V×Support n=> B.fire i.1) (fun i _=> Finset.singleton_nonempty _) (fun i=> ψ i.1 i.2 U)).symm
   · exact fun _ h=> (hv _|>.permits U h).2
   exact fun _ => husk ψ B hs _ _
lemma reversal (U:Config G n)(h:(F U).part B.quiet=0) : play A B K F U=play A B κ (F-J') U:=by
   unfold play; rw [arranged A ψ K hs hv U]; let y : Poly B := (F-J') U; let z:= J' U; have hx : (F U)=y+z:= (sub_add_cancel ..|>.symm)
   have he:y.part B.quiet=0:=by
       have ht:z.part B.quiet=0:=by unfold z kelp; simp [Poly.part_sum,corn_quiet ψ B]
       have hs:y.part B.quiet= (F U).part B.quiet-z.part B.quiet:=rfl; rw [hs,h,ht,sub_zero]
   nth_rw 1 [hx]; rw [pass_add he (show z.part B.quiet=0 from (by unfold z kelp; simp [Poly.part_sum,corn_quiet ψ B]))]; unfold z y; congr 1; ring
include h hr
omit hs in
lemma posts (U:Config G n)(i:V)(j:Box n): (κ j U).part (B.fire i)= (K j U).part (B.fire i)+hook A.activities A.p.threshold (ψ i) j U:=by
   rw [snow _ _ _ _ U j (fun i=> (hv i).permits U) _ (fun i=>h i U) (corn_quiet ψ B U) _ (mass_crest _ hr _),Fintype.sum_prod_type]; congr 1; rw [Finset.sum_eq_single i]; unfold hook; simp [conviction]
   · intro b _ hb; simp [conviction,hb.symm]
   simp
variable {W S C μ a z u : ℝ}
local notation "T0"=> A.p.threshold
local notation "R0"=> A.p.B
-- exact existence after projection, independently Pareto bounds n. Need F+ci.. Setting d<E, etc by user.
lemma closeup {M:ℕ}{H:Support n→Config G n→Poly B}
    (h0:∀ x,(F x).part B.quiet=0)(hH:∀ U (p:B.Mode), 2 ≤ p.val.card → (F U).part p=(∑ i,H i U).part p)
    (hw:∀ i,0<w i)(hu:0≤ c)(hh:Occupancy o M)(hY:∀ p,Burns o p (H p) A.p.threshold)(hE:Towed w id H A.p.B (d+μ) S)(hK:Towed w Prod.fst K A.p.B e W)
    (hq:e=d+μ+z)(hf:0 ≤ d+μ) (hp:((A.p.B + A.p.B +1:ℕ):ℝ)^4*(W+M*siteFactor A.p.B*c)≤z)
    {w':V→ℝ}(hw':∀ i,0<w' i)(hg:Repegs o A.p.B w w' μ a B)(ha:0≤a)(hc:a*S ≤ C)(hc':a*(Real.exp (W+M*siteFactor A.p.B*c)-1) ≤ C)
    (hZ:∀ i j U,(K i U).part (B.fire j)+hook A.activities A.p.threshold (ψ j) i U=profile A.activities (k j) i U)
    (ht:∀ i U,(play A B K F U).part (B.fire i)=coin A (Φ i) (k i) U)(hy:∀ i,Dominated (k i))(hit:∀ U,A.eval U≠0): Served A Φ (fun i=>profile A.activities (k i)) (play A B K F) o w' d C:=by
   let U₀:=conviction ψ B
   have hF(i):=threshed K U₀ Prod.snd T0 hv (dresses ψ B hs) i
   have hB : Towed w Prod.fst κ R0 (d+μ) (Real.exp (W+M*siteFactor A.p.B*c)-1) := branch K U₀ Prod.snd (A.p.threshold) w (hq ▸ hK) (hq ▸ stock ψ B hs hw hh hu) hw hf hp
   have hu:play A B K F=play A B κ (F-J'):=funext fun U=>reversal A ψ K F hs hv U (h0 U)
   obtain ⟨he,hv⟩:=plank A B κ (F-J') Φ k hr (H:=H) (o:=o) (fun i U=> (wine K U₀ Prod.snd T0 _ i (fun p=>hv p|>.permits U) (corn_quiet ψ B U)).trans (h i U)) (fun U=>(by simp only [Pi.sub_apply,part_sub,kelp,Poly.part_sum,h0,corn_quiet ψ B,sum_const_zero,sub_zero])) hY hF hy (fun i U j=>(posts A ψ K hv h hr U i j).trans (hZ ..)) (fun i U=> hu ▸ ht i U) hit (fun U p hp=> by simp only [Pi.sub_apply,part_sub,kelp,corn_light ψ p hp U,sub_zero,hH U p hp])
   · refine ⟨_,_,he,?_,?_,hu.trans hv⟩
     · exact ((hE.sift.peg (fun i=> (he.exp i).1.toBorne) (fun i=>(he.exp i).2) hg hw hw' ha)).shrink le_rfl hc hw'
     exact ((hB.sift.peg (fun i=> (he.flag i).1.toBorne) (fun i=>(he.flag i).2) hg hw hw' ha)).shrink le_rfl hc' hw'
end YM.MergeProof.Accent

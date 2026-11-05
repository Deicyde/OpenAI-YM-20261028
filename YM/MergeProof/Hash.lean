import YM.MergeProof.Appl
import YM.MergeProof.Flax
import YM.MergeProof.Grant
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable [Fintype ι](q:ι→ Hat B R) (S:StepData c f) {σ t c' e d C : ℝ} {r : V→ℝ}
local instance : IsTopologicalSemiring (Poly B):=⟨⟩
variable (h: R.Lawful σ C t e c')
include h
def board (p:Box f)(U:Config G f):=∑' i:{i//barcode R.activities i=p},rush q (.gasKey i.val) U
omit h in
lemma chair (U:Config G f): Summable fun i=>rush q (.gasKey i) U:= summable_of_ne_finset_zero (s:=gasDeck q) (fun i hi=> rush_vacuous _ _ U fun j hz=> hi ((slots q _).2 ⟨j,hz⟩)) -- edit
lemma fence (hp:∀ i,0 < r i)(U: Config G f): Summable (fun i=>Poly.price r (Kunt q i U)) ∧ Summable (fun i=>Kunt q i U):=by
   let a i:Poly B:= Poly.bead B (R.activities.K i U); have hs: Summable fun i=>Poly.price r (a i):=by
      simp only [a,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real]; exact (mass_crest _ h.labels U).norm
   have ht(i)(hi:i∉gasDeck q): Poly.price r (rush q (.gasKey i) U)=0:=by rw [rush_vacuous _ _ U (fun j hj=> hi ((slots _ _).2 ⟨j,hj⟩)),Poly.zero_price]
   have he:Summable (fun i=>Poly.price r (Kunt q i U)):= (hs.add (summable_of_ne_finset_zero ht)).of_nonneg_of_le (fun i=>Poly.nonnegative hp _) (fun i=>Poly.addition hp ..)
   exact ⟨he,(Poly.budgeted hp he (fun i=>le_rfl)).1⟩
lemma sectioned (U:Config G f): Summable (fun k:Finset ℕ=> if R.activities.admissible R.p U k then ∏ i∈k,Kunt q i U else 0):= ((Packets.summable_value _ _ _ (w:=fun _=>1) (fun _=>zero_lt_one) (fence q h (r:=fun _=>1) (fun _=>zero_lt_one) U).1)).congr (shovel R.activities (fun i=>Kunt q i U) U R.p)
lemma win (U:Config G f): cram (barcode R.activities) (fun i=>Kunt q i U)=fun p=> bar R.activities B U p+ board q p U:=by
   funext p; let s i: Poly B:=Poly.bead B (R.activities.K i U)
   let b := barcode R.activities; let k i:= R.activities.K i U
   have hz: Summable s:=by
      let w(V:V):=(1:ℝ); have hv: Summable fun i=> Poly.price w (s i):=by simp only [s,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real];exact (mass_crest _ h.labels U).norm -- dup
      exact (Poly.budgeted (w:=w) (fun _=>zero_lt_one) hv (fun _=> le_rfl)).1
   have hg:= chair q U
   unfold cram Kunt; rw [Summable.tsum_add];
   · exact congr_arg (·+board q p U) (by
       ext i; rw [Poly.share (f:=fun i:{i// barcode R.activities i=p}=> s i.val) (hz.comp_injective Subtype.val_injective)]; unfold bar profile cram; by_cases ht:i=B.quiet <;> simp [s, Poly.bead,ht])
   · exact hz.comp_injective Subtype.val_injective
   exact hg.comp_injective Subtype.val_injective
lemma passIn (hp:∀ i,0 < r i)(U:Config G f) : Merge.Photo.given (S:=S) (fun i=>(q i).M) (fun i=>sumFee (q i) r) B (fun i=> sing (q i) r) U=(Real.exp (R.exponent U):ℂ) • (jets q U*field (fun i=>bar R.activities B U i+board q i U) (RG.flags R.p.threshold U)):=by
   let P k:= if R.activities.admissible R.p U k then ∏ i∈k,Kunt q i U else 0
   let f(i : Tickets (Palette.sign (fun j=>(q j).M) S)) (k):= ash q S r i U k
   have ht:= sectioned q h U
   let g:=jets q U
   have he: ∑' k,g*P k=g*field (fun i=> bar R.activities B U i+board q i U) (RG.flags R.p.threshold U):=by rw [← win q h U,rock_out R.activities R.p U (fun i=> Kunt q i U) hp (fence q h hp U).1]; exact (ht.hasSum.mul_left _).tsum_eq
   have hf(i): Summable (f i):=by
      let M0:= team (fun j=>(q j).M) i; let c:= ∏ j∈ i.val,sumFee (q j) r
      exact ((Complex.ofRealCLM).summable (((M0.bud h).summable U).mul_right c)).smul_const _ -- edit
   unfold Merge.Photo.given; rw [show (jets q U)=g from rfl, ← he]; simp_rw [show ∀ k,g*P k=_ from fun k=>cliff q S hp U k]; rw [Summable.tsum_finsetSum (f:=fun i k=>ash q S r i U k) (hf:=fun i _=>hf i),Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
   unfold ash Team.cicada; let u t:ℂ:=↑((team (fun j=>(q j).M) i).bun t U*∏ j∈i.val,sumFee (q j) r)
   let A:=∏ j∈i.val, sing (q j) r; let κ(t):ℂ:=u t
   have hp':Summable κ:= (Complex.ofRealCLM).summable (((team (fun j=>(q j).M) i).bud h).summable U |>.mul_right _)
   rw [show ∑' v,(↑((team _ _).bun v U * (∏ j∈i.val,sumFee (q j) r)):ℂ) • (∏ j∈i.val,sing (q j) r)=(∑' i,κ i) • A from (hp'.hasSum.smul_const A).tsum_eq, ← mul_smul]; congr 1; unfold κ u; rw [← Complex.ofReal_tsum,tsum_mul_right,mul_assoc,Complex.ofReal_mul]
end YM.MergeProof.Menu

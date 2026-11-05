import YM.FullVolume.Fields.Peat
import YM.FullVolume.Fields.Inlay
import YM.FullVolume.Fields.Lofts
import YM.FullVolume.Fields.Cowl
/-! Slices of stripped density: when mixing wavelengths we compare with the activity package of SAME step, not reset after. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Ac
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations MergeProof MergeProof.Accent MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open Marker Finset Urns Overlay
variable {G:Gauge}{n:Side} (R:ℕ→Rep G n)
def cold (R : Rep G n)(U:Config G n):= Real.exp (R.exponent U-R.scalar)
def coals (R:Rep G n)(U:Config G n):= Real.exp (-R.scalar)*R.eval U
def lack (R:Rep G n):ℝ := ∫ U,coals R U ∂prior G n
local notation "Λ"=> (0:Site n)
variable {S:Urns.Price G n}{u r: ℕ→ℝ} {σ c v w b k:ℝ}{h:Clip}
open Stationary Artes
structure Flux (p:ℕ → Rep G n) (S:Urns.Price G n)(h:Clip)(σ c C e v:ℝ): Prop where
    lawful: ∀ᶠ n in atTop,(p n).Lawful σ c C e v
    paid: ∀ᶠ n in atTop,(p n).p=S.p∧ (p n).clip=h
    volume: ∃ x: ℕ→ Show S,CauchySeq x ∧ ∀ᶠ n in atTop, (p n).activities=(x n).proper
    beta : CauchySeq fun n=> (p n).beta
    trails : ∃ p':PathData G,∃ v':ℝ, p'.Bounds h σ c C ∧0<v'∧∀ g>0,∀ᶠ n in atTop,Rios (p:=(p n).path) (q:=p') v' g
namespace Flux
variable (H:Flux R S h σ c v b k)
include H
set_option maxHeartbeats 480000 in
lemma lawsT : Confluence (fun i=> cold (R i)):=by
    obtain ⟨p,s,hQ,hP,ht⟩:= H.trails; obtain ⟨a,ha,hA⟩:= H.volume
    have hl :∀ᶠ n in atTop,(R n).path.Bounds h σ c v:= (H.lawful.and H.paid).mono fun i hi=> (hi.2.2 ▸ hi.1.paths : _)
    let β(i):=(R i).beta; let p i (U:Config G n):= (R i).path.inChannels h S.p (β i) U; have hv:Confluence p:= rents S.p hQ hP hl ht n H.beta
    let s i:= (a i).proper.additive S.p; have hp:Confluence (fun i U=> Real.exp (- p i U-s i U)):= ((hv.dual (vases ha)).ahead (fun z=> Real.exp (-z.1-z.2)) (by fun_prop))
    refine hp.persist ((hA.and H.paid).mono fun i hi=> ?_); funext U
    unfold cold p s Rep.exponent Rep.scalar; dsimp only; rw [hi.2.1,hi.2.2,hi.1]; congr 1; unfold β; ring
omit H
variable {V:Type}[DecidableEq V][Fintype V](B:Census V)
local instance : ProperSpace (Poly B):= inferInstanceAs (ProperSpace (B.Mode→ℂ))
include H
lemma billing (i:Box n) : Confluence (fun n U=> bar (R n).activities B U i):=by
    obtain ⟨p,hp,h⟩:= H.volume
    let f i' U:=Poly.bead B (profile (p i').proper (fun j=> Complex.ofReal ∘ (p i').proper.K j) i U)
    refine ((logK hp i).ahead (fun x=> Poly.bead B x) (Sever.smeasure _)).persist (h.mono fun i hi=>?_) ; funext U; unfold bar; dsimp only; rw [hi]
lemma boarded (X:ℕ→ Box n→ Config G n→Poly B)(hp:∀ i,Confluence fun n U=> X n i U): Confluence fun i U=>field (fun j=> X i j U) (flags (R i).p.threshold U):=by
    let t(i:ℕ)(b: Finset (Box n)) U:= Accent.grid (fun j=> X i j U) (flags S.p.threshold U) b; have hf(b: Finset (Box n)):Confluence fun n U=> t n b U :=by
        unfold t grid; apply Confluence.ifs _ (Confluence.metal 0) (fun U=>Pattern (flags S.p.threshold U) b); exact Confluence.wreaths b hp
    refine (Confluence.fences (p:= fun b n U=> t n b U) Finset.univ hf).persist (H.paid.mono fun i hi=>?_); funext U; dsimp only; rw [hi.1]; rfl
include B
lemma fanned: Confluence fun i=> coals (R i) :=by
    let f i U:= ((R i).activities.gas (R i).p U:ℝ); let t i U:= field (fun j=> bar (R i).activities B U j) (flags (R i).p.threshold U)
    have hb:Confluence t:= H.boarded R B (fun i j U=> bar (R i).activities B U j) (H.billing R B)
    let g i U:= ((t i U).part B.quiet).re; have hg:Confluence g:= (hb.ahead (fun i=> (i.part B.quiet).re) (Complex.continuous_re.comp (Poly.part_cont _)))
    have hf : Confluence f:= hg.persist (H.lawful.mono fun i hi=>by funext U; unfold g t; rw [show field (fun j=> bar (R i).activities B U j) (flags _ U)=Poly.bead B ↑(f i U) from hawk (R i).activities _ B hi.labels U]; simp [Poly.bead])
    refine ((lawsT R H).lit hf).persist (Eventually.of_forall fun i=>?_); funext U; unfold cold f coals Rep.eval; dsimp only; rw [sub_eq_add_neg,add_comm (R i|>.exponent U), Real.exp_add,mul_assoc]
lemma lacks: CauchySeq fun i=> lack (R i):= by
    apply Confluence.account (prior G n) (H.fanned R B); filter_upwards [H.lawful] with i hi; exact (measurable_const.mul (R i|>.envelope hi|>.meas)|>.aestronglyMeasurable) -- explicit value
end Flux
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.Flux.lacks

import YM.FullVolume.Fields.Till
/-! Unity ratio test. For ANY repeated orbit at same cutoff slices; receipt = stamp of torn (erase grade≥2) prior, freeze scalar independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Ac
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations MergeProof MergeProof.Accent MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open Marker Finset Urns Overlay
variable {G:Gauge}{n:Side}
variable {V:Type}[DecidableEq V][Fintype V] {B:Census V}
variable (R:Rep G n) (P:V→ Config G n→ℂ)(F:V→ Box n→ Config G n→ℂ)
def toll (B:Census V)(U:Config G n): Poly B:= (Real.exp (-R.scalar):ℂ) • (restore R P F 0 0 U)
lemma voter (i:B.Mode)(U:Config G n):
      (toll R P F B U).part i= (cold R U:ℂ)* (Poly.pass (Mach B (fun j=>P j U)) * field (fun j=>bar R.activities B U j+Mach B (fun k=> F k j U)) (flags R.p.threshold U)).part i:=by
    unfold toll restore; simp only [Pi.zero_apply,sum_const_zero,add_zero, Poly.part_smul]; rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,cold,show - R.scalar+R.exponent U= R.exponent U - R.scalar from by ring]
lemma vote {σ c C v k:ℝ} (i:B.Mode)(he:R.Lawful σ c C v k)(hy:∀ i, Measurable (P i))(hp:∀ i j,Measurable (F i j)): Measurable (fun U=> (toll R P F B U).part i):=by
    let o:V→Site n:=fun _=>0; let z:(Support n)→ Config G n→Poly B:=0; let y:Box n→ Config G n→ Poly B:=0
    have h:Carton o z y R.p.threshold := ⟨fun i=> ⟨⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun i=> measurable_const,fun U i _=> rfl⟩,fun U h=>False.elim (h rfl),fun U=>rfl⟩,fun U i hi=>False.elim (hi rfl)⟩,fun i=>⟨⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun i=>measurable_const,fun U i _=>rfl⟩,fun U h=>False.elim (h rfl)⟩,fun U i hi=>False.elim (hi rfl)⟩⟩
    have hm:= (Poly.part_cont i).measurable.comp (Sever.meas P F hy hp he h); simp_rw [toll,Poly.part_smul]; exact measurable_const.mul hm
variable {R P F}
def mid (R:Rep G n) (P:V→ Config G n→ℂ)(F:V→ Box n→ Config G n→ℂ)(i:B.Mode):ℂ:= (∫ U,(toll R P F B U).part i∂prior G _)/(lack R:ℂ)
lemma reply (A:History G) {N p m:ℕ}(h:A.Selected)(hx:m≤N) (P: V→ Config G (A.S.side m p)→ℂ) (F:V→ Box (A.S.side m p)→ Config G (A.S.side m p)→ℂ)(i:B.Mode): mid (A.rep N p m) P F i=Sever.stamp A N p m (restore (A.rep N p m) P F 0 0) i:=by
    unfold mid Sever.stamp; rw [taps A h m p N hx]; simp_rw [toll,Poly.part_smul]; let x:=Real.exp (-(A.rep N p m).scalar); have hp : (x:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    rw [integral_const_mul,stripped, Complex.ofReal_mul,mul_div_mul_left _ _ hp]
namespace Confluence
local instance : ProperSpace (Poly B):= inferInstanceAs (ProperSpace (B.Mode→ℂ))
variable (p:ℕ→ Rep G n) {D:Urns.Price G n}{u:Clip}{σ c C e v :ℝ}
variable (f:ℕ→V→ Config G n→ℂ)(g:ℕ→V→Box n→ Config G n→ℂ) (h:Flux p D u σ c C e v)(he:∀ i,Confluence (fun n U=> f n i U))(hv:∀ i j,Confluence (fun n U=>g n i j U))
include h he hv
lemma psalms (i:B.Mode): Confluence fun n U=> (toll (p n) (f n) (g n) B U).part i:=by
    simp_rw [voter]; let P' n U:= Mach B (fun j=> f n j U);let Γ n j U:= Mach B (fun k=> g n k j U)
    have hm{P:ℕ→V→ Config G n→ℂ} (hp:∀ i, Confluence fun n x=> P n i x):Confluence (fun n x=> Mach B (fun j=> P n j x)):= Confluence.fences (p:=fun j n x=>Poly.send (B.fire j) (P n j x)) _ (fun j=> (hp j).ahead (Poly.send (B.fire j)) (Sever.smeasure _))
    let V' n U:= field (fun j=>bar (p n).activities B U j+ Γ n j U) (flags (p n).p.threshold U); have hf:Confluence V':= h.boarded p B _ (fun i=> ((h.billing p B i).bats (hm (P:=fun n j=>g n j i) (fun j=> hv ..))))
    exact ((h.lawsT p).ahead Complex.ofReal Complex.continuous_ofReal).lit ((((hm (P:=f) he).ahead Poly.pass Poly.pass_cont).lit hf).ahead _ (Poly.part_cont _))
-- fractions.Try generic EOS.complete ratio
lemma laven (i:B.Mode){a:ℝ}(hp:0<a)(hs:∀ᶠ n in atTop,a ≤ lack (p n))(hm:∀ᶠ n in atTop,∀ j, Measurable (f n j)∧ ∀ i,Measurable (g n j i)): CauchySeq (fun n=> mid (p n) (f n) (g n) i):=by
    have hr:= h.lacks p B; have ht:= (psalms p f g h he hv i).account (prior G n) ((hm.and h.lawful).mono fun n hn => (vote (p n) _ _ i hn.2 (fun i=>(hn.1 i).1) (fun i=>(hn.1 i).2)).aestronglyMeasurable)
    obtain ⟨u,hu⟩:= cauchySeq_tendsto_of_complete hr; obtain ⟨x,hX⟩:= cauchySeq_tendsto_of_complete ht; have he:0<u:= hp.trans_le (ge_of_tendsto hu hs); exact (hX.div (Complex.continuous_ofReal.continuousAt.tendsto.comp hu) (Complex.ofReal_ne_zero.mpr he.ne')).cauchySeq
end Confluence
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.Confluence.laven
#print axioms YM.FullVolume.Retreat.reply

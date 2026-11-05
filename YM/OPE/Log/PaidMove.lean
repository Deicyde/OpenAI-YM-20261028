import YM.OPE.Sweep.Step
/-! # Paid even without universal aperture bound; use Repegs -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {Z V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}

variable {A:History G}{N p k i:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E:∀ i:ℕ, V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:∀ i:ℕ,V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "Γ" => A.levels.clock.op i p
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
variable {Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}
variable (h:A.Selected)(ht:Thor A δ r D σ χ k)
include h ht
local notation "L" => ((A.S.block i).val:ℝ)
local notation "e" => (Y' i).supportExponent
local notation "x" => (6*L:ℝ)
lemma Under.passes (hi:k ≤ i)(hn:i<N) (hc:Under A N p E o P v B Q (i+1) hn W c)
    (hf: E (i+1)=fun j=>(Γ).ratio.embed (E i j))
    (hb:∀ j,j≠v→∀ b:I,o (i+1) (j,b)=affine (P j).1 (E (i+1) j) (o (i+1) (v,b)))
    (hΔ: Q i hn.le=(Γ).push (R (i+1)).beta (Q (i+1) hn))
    (hp:Integrable (Q (i+1) hn) (prior G _))
    (hx: (Γ).ratio.parent ∘ o (i+1)=o i) (hV: Occupancy (o (i+1)) (r i)) (hg:Occupancy (o i) (r i))
    (hY: MergeProof.Float.Runs (D N p i hn) Γ x)
    (he:x ≥ 1)
    (hPeg: Repegs (o i) (Y' i).B (fun j=>δ i*(W ∘ Prod.snd) j) (W' ∘ Prod.snd) (1/2) 1 (Names V I))  (hw:∀ j,x * W' j ≤ W j) (hW:∀ j,0<W' j): Live A N p E o P v B Q δ χ i hn.le W' c:=by
    have ha(j:I):W' j ≤ W j:= (le_mul_of_one_le_left (hW j|>.le) he).trans (hw j)
    obtain ⟨g,K,hb',hd,he',hR⟩:=hc.flor; have hA:= ht.suns i hi; obtain ⟨hK,hh⟩:=ht.moon N p i hi hn
    let d(b:I):=(1:ℝ)/(2*W b); have hv(j:V×I):2*(W ∘ Prod.snd) j*d j.snd ≤1:= by change 2*W j.2*(1/(2*W j.2))≤1; rw [mul_div_cancel₀ _ (by have he:= hc.width j.2; positivity)];
    obtain ⟨g',F,hG,hF',hφ,hC,hU⟩:= flaring A r h hn hA hK hh (fun (j:V×I)=>hc.width j.2) (hf ▸ hR) (by linarith only) hV (hx.symm ▸ hg) (fun _ _ _=>rfl) (fun j hj b=> by rw [show _=E (i+1) j from (congr_fun hf j).symm]; exact hb j hj b) (hf ▸ he') hd hb' hv hY (zero_le_one.trans he) hp
    have hT:=descended A N i p r h hn hA (fun j=>hc.width j.2) (fun j=>hW j.2) (hx.symm ▸ hg) (hx.symm ▸ hPeg) hU hG hF'
    rw [hx,← hΔ] at hU hT
    have hA' j: W' j.2*‖c j‖≤1:= (mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)).trans (hc.affordable j)
    refine ⟨⟨hW,hA',g',F,fun j=>?_ ,hG,hφ,hT⟩,g',F,hU.reprice (fun j=>mul_le_mul_of_nonneg_left (ha _) hA.hats.1.le) (fun j=> mul_nonneg hA.hats.1.le (hW _|>.le))⟩
    have hv:=hC j; rw [hx] at hv; apply hv.more; change x*(1/(2*W j)) ≤ 1/(2*W' j); rw [← mul_div_assoc]; have hP:=hc.width j; have ht:=hW j; exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [hw j])

end YM.MergeProof.Ribbons.ManyCopies

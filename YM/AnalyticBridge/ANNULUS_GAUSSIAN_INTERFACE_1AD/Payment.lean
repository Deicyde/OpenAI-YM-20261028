import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Halos
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Tariffs

/-!
# E:eq:pmult -- local packet payment theorem on the dyer

A substantive output at zero derivatives, throughout the authentic band.
Permits rho to hold additional post-L prices (e.g. an auxiliary C_L per
site costs in poly(B)/seed; none implicitly given that don't come from
the true factors in offer). Applies even though some costs here (e.g.
 second log) lack a controlled *ordered expansion*: priced the
window terms themselves pointwise, not the leftover relative log.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset Scales Affine
open scoped YM.Next.SectorChange.Completion
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (T : Tube G S) (V : Config G c) (x : ℝ) (A O : Stores S) (k : S.Choices) (F : Forest S.ratio) (q : Chi)
variable (R : Rep G f) (W width : ℝ) (Z : ChartRatio G) (qS : Chi)
variable (P : Teller G) (L : Side) (κ H ρ G₀ μ v : ℝ)
variable (yH : LinkArray G (Frozen A x F))
variable (D α n : ℕ)
variable (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
variable (J : Finset ℕ) (z : Prices G (Active A x F))

-- packs Cleans_at at given x, released later similarly for any height
/-- The local chart view needed at use. Earn at post-L thresholds
from Affine.Cleans. Quantifies still on true physical stencils and
profiles -- this does NOT ask for sharp boundaries or analyticity
off Wide. -/
def Seen (P : Teller G) (L : Side) (W width x : ℝ) :=
    ∃ K : ℝ,1≤K ∧ K≤width ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
      S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (D : ℕ) (F : Forest S.ratio) (O A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Wide O A D x W U k V → ∃ a : Directions G f,
        ∀ p : Site c,inSweep O A D (radiusB x) p → Cleans (S:=S) K x U V p a

lemma started (h : 0<W) : ∃ K : ℝ,1≤K ∧
    ∀ width ≥ K, ∀ᶠ x : ℝ in atTop, Seen P L W width x := by
  obtain ⟨u,hu,H⟩:=cleans_at P L W h
  refine ⟨u,hu,fun width hw => ?_⟩
  filter_upwards [H] with x hx
  refine ⟨u,hu,hw,?_⟩
  intro c f S T hl hs ht D F O A U k V h1 h2
  obtain ⟨a,-,hh⟩:=hx c f S T hl hs ht D F O A U k V h1 h2
  exact ⟨a,hh⟩

set_option maxHeartbeats 400000 in
theorem payment
    (hD : 2≤D) (hL : S.patch.L=L) (hs : 100*(1+radiusB x)≤c.val)
    (hn : rollRate S.patch Z D μ v + G₀ ≤ H)
    (ha : P.Funds S T) (ht : PointCharge T x W κ)
    (h : Affine.Ledger P L W κ (2*width) H 4 D x) (he : Seen P L W width x)
    (hF : granting P S.patch μ v x)
    (hV : A.flags=RG.flags (temp x) V)
    (hI : ∃ B : ℝ, Authorized A V F x B)
    (hβ : R.beta∈Set.Icc (y G L x/2) (2*y G L x))
    (hb : Packet O A α) (hα : (D+5)*radiusB x≤α) (hr : span S.patch x≤radiusB x/50)
    (hw : 0<W) (hp : 0<fiery G x S.patch.L)
    (hZ : LocalRatio Z) :
    let d := width*fiery G x S.patch.L
    let N := O.dome ((D+100)*radiusB x)
    let Nf:=covered N S; let Nc:=nearNoise N
    let a:=m yH+coupling R.beta • z; let U:=landed x A F V yH a
    let B := offer T V x A O k F q R W d Z qS yH D v m J z
    0<d → d<firstRadius G → 4*d<Z.radius → ρ ≤ coin G L G₀ 4 x * O.shares →
    0 ≤ B ∧
    Real.exp ρ * mint S N Nc * ‖B‖ ≤ Real.exp (-κ/4*(p G L x)^2*O.shares) ∧
    Real.exp ρ * mint S N Nc * ‖B‖ ≤ Real.exp (-κ/4*(p G L x)^2*O.shares) *
        (receipts qS A x W N (nearFace S N) Nc U V k * capsule x A F q d Z (locals A O x F ((D+104)*radiusB x)) (tape a) * voids R.activities R.p U J Nf) ∧
    (B≠0 →
      (∀ s : Signed, Wide (turnStore s O) (turnStore s A) D x W (pull s 0 U) (choice s k) (pull s 0 V)) ∧
      (∀ s, (harvest A O x F s D).written T x (choice s k) (pull s 0 V) (signedArray x A F q d V yH a s)) ∧
      (∀ i∈Nf,i∈RG.flags (fiery G x L) U → ∃ p∈A.costs,i∈RG.touched p) ∧
      (∀ i∈Nf,i∉J.biUnion (fun j => (R.activities.forced j).support) → i∉RG.flags R.p.threshold U)) := by
  intro d N Nf Nc a U B hd hfirst hx hρ
  let E := nearFace S N
  let r:= (D+104)*radiusB x
  let y' := tape a
  let w:=receipts qS A x W N E Nc U V k
  have hk : w∈Set.Icc (0:ℝ) 1 := receipts_unit qS A x W V N E Nc U k (funds_branch ha)
  let c':=capsule x A F q d Z (locals A O x F r) y'
  let u:=voids R.activities R.p U J Nf
  have hu : u∈Set.Icc (0:ℝ) 1 := unit_alphabet _ _ (fun i _ => vflag_price ..)
  have hi : c'∈Set.Icc (0:ℝ) 1 := capsule_le x A F q d Z _ _ hZ hd hx
  have h₀ := unit_product (unit_product hk hi) hu
  let frame:=fun s: Signed => anchorage (turnStore s O) (D*radiusB x)
  let e:= emission T V x A k F q d yH frame R.beta (m yH) z
  let t:= ∑ i∈everyLink S O (D*radiusB x),couple T V x k A F v i
  let g:= grab x A F R Z (driftwood A O x F)
  have hB : B = w*c'*u*Real.exp (e+t+g) := rfl
  have h1 : 0 ≤ B := hB.symm ▸ mul_nonneg h₀.1 (Real.exp_pos _).le
  refine ⟨h1,?_⟩
  simp only [Real.norm_of_nonneg h1]
  obtain ⟨hμ,hμ',hv,hB',hY,hQ⟩:= hF
  obtain ⟨hr',hs',-⟩ := hQ S T rfl hs ha A F V k hV
  obtain ⟨X,HX⟩:=hI
  by_cases hz : B=0
  · exact ⟨by rw [hz,mul_zero]; exact (Real.exp_pos _).le,by rw [hz,mul_zero]; exact mul_nonneg (Real.exp_pos _).le h₀.1,fun H => (H hz).elim⟩
  have H₁ : w*c'*u≠0 := by rw [hB] at hz; exact left_ne_zero_of_mul hz
  obtain hC := left_ne_zero_of_mul H₁
  have h₂ : w ≠ 0 := left_ne_zero_of_mul hC
  have h₃ : admitsHere A O x F q d y' r ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hC)
  have h₄ : u ≠ 0 := right_ne_zero_of_mul H₁
  have hh : O.dome ((D+5)*radiusB x)⊆N := farther (Nat.mul_le_mul_right _ (by omega))
  have hf s := force_wide (funds_branch ha) hw hp hh h₂ s
  obtain ⟨K,hK,hk',hG⟩ := he
  have hS s := hG S T hL hs ha D (turnForest s F) (turnStore s O) (turnStore s A) (pull s 0 U)
    (choice s k) (pull s 0 V) (turn_sliced s F U (fun e he => F.on_tree _ ⟨e,he⟩)) (hf s)
  obtain ⟨hE,hA⟩:=depositing T V O q ha hL hs ht h HX hβ hb hα hD (m yH) z hr hf
    (show (2+D)*radiusB x≤r from Nat.mul_le_mul_right _ (by omega)) h₃ hd hfirst ⟨K,hK,hk',hS⟩
  let hq:= mint S N Nc
  let M:=coin G S.patch.L H 4 x * O.shares
  have hY : 1<y G S.patch.L x := hL.symm ▸ h.1
  rw [← hL] at hρ hE hβ
  have hm := roll_cover T V k A O F Z R (D:=D) (C:=H-G₀) (show 1≤radiusB x by omega) hμ (hμ'.trans hv) hr' hs' hZ.scale hY hβ (by linarith)
  have he : ρ + (t+g+Real.log hq) ≤ M := by
    have h0 := add_le_add hρ hm
    change ρ + (t+g+Real.log hq) ≤ _
    apply h0.trans_eq; unfold M coin; ring
  let A':=κ/4*p G S.patch.L x^2*O.shares
  have hE' : e ≤ -A' - M := by
    have h1 : Real.exp e ≤ _ := hE
    apply (Real.exp_le_exp.mp h1).trans_eq; unfold A' M; ring
  have hpay : Real.exp ρ * mint S N Nc * B ≤ Real.exp (-κ/4*(p G L x)^2*O.shares)*(w*c'*u) := by
    rw [← hL,hB]
    calc
      _ = Real.exp (ρ + (t+g+Real.log hq) + e)*(w*c'*u) := by
        simp_rw [Real.exp_add,Real.exp_log (show 0<hq from mint_pos k N Nc)]; unfold hq; ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) h₀.1
        unfold A' M at *; linarith only [hE',he]
  refine ⟨hpay.trans (mul_le_of_le_one_right (Real.exp_pos _).le h₀.2),hpay,
    fun _ => ⟨hf,hA,fun i hi hh => ?_,fun i hi hh => ?_⟩⟩
  · rw [← hL] at hh; exact local_flagged h₂ hp i (mem_filter.mp hi).2 hh
  exact violation h₄ hi hh

end YM.AnalyticBridge.Annulus1AD

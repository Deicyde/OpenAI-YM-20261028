import YM.FullVolume.Spiral.Hessian
import YM.FullVolume.Spiral.North
/- index geometry grade clocks. pre-L size for coherent art. Loom follows separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
open Forum
open Extra.Histories.InputColumn
open UniformSpace FullVolume.Amp
local notation "I"=> Extra.Histories.InputColumn.Listing
open Beam PaidBeam Input Org RG.Supply
variable {S:ℕ→RG.Stage} {s:Sheet G}{T:ℕ→ℝ}{q:ℝ}
open Push.PriceCompiler
/-- These costs (S prior!) include inverse propagation per step. May reserve stronger via Agenda knob. hχ no arbitrary prices circular. -/
structure Request (G:Gauge) (S:ℕ→ RG.Stage) (T:ℕ→ℝ)(Φ :Tableau q 300) (X:ℕ→ℕ→ℝ)(i j k:ℕ)(L:Side):Prop where
   rev:revenue ((Labels.frames G).level k) Φ.price (Doors.rate L) (X k j) * (T j*Tower.χ ((Labels.frames G).level k)) ≤ 1/2
   price:heat ((Labels.frames G).level k) Φ.price (Doors.rate L) (T j) (Local.turnCost (S i).order (S i).power) (X k j)*(2*(T j*Tower.χ ((Labels.frames G).level k))) ≤ X k i
   enough : (2 * (T j *Tower.χ ((Labels.frames G).level k))) ≤ L.val
   noted : max (X k i) (X k j) ≤ L.val -- may pay also protocol.Height growth.
structure Sav (G:Gauge)(S:ℕ→RG.Stage) (T:ℕ→ℝ)(Φ:Tableau q 300)(X:ℕ→ℕ→ℝ) (L:ℕ→Side):Prop where
   zero k i : 2*Tower.χ ((Labels.frames G).level k) ≤ X k i
   gets {i j k:ℕ}:StepStages j i → k+3≤ i → Request G S T Φ X i j k (L j)
-- This is from rounding BEFORE L. Discrete axes may even tie. chosen L layout after.Specific all widths use this same T.Theta
variable (G) (S:ℕ→RG.Stage) (T:ℕ→ℝ) (Φ:Tableau q 300)
private abbrev levy(k i j):= densityP ((Labels.frames G).level k) Φ.price (Local.turnCost (S i).order (S i).power) (T j) * (2*(T j*Tower.χ ((Labels.frames G).level k))) -- number
-- Ω once
private theorem fuel (V:ℕ→ℕ→ℝ)(i j k:ℕ)(hp: levy G S T Φ k i j < V k i): ∃ t:ℕ,∀ L:Side,t ≤ L.val→ Request G S T Φ V i j k L:=by
    let f n:= (n:ℕ) |> fun i=> (i:ℝ)^(-(2/5:ℝ)); have hf: Tendsto f atTop (𝓝 0):=(tendsto_rpow_neg_atTop (show 0 < (2/5:ℝ) by norm_num)).comp tendsto_natCast_atTop_atTop; let W:= (Labels.frames G).level k; let X:= S i; let Y:=levy G S T Φ k i j; let t':=Φ.price; let c:=Local.turnCost X.order X.power; let r:=T j*χ W
    have hv:Tendsto (fun i:ℕ=> revenue W Φ.price (f i) (V k j)*r) atTop (𝓝 0):=by
       let e(x:ℝ):= revenue W Φ.price x (V k j)*r; have he:Continuous e:=by unfold e revenue; fun_prop
       have hx : e 0=0:=by unfold e revenue; ring
       exact hx ▸ ((he.tendsto 0).comp hf)
    have hY : Tendsto (fun n:ℕ=> heat W t' (f n) (T j) c (V k j) * (2*r)) atTop (𝓝 Y):=by
       let e(x:ℝ):= heat W t' x (T j) c (V k j)*(2*r); have he:Continuous e:=by unfold e heat; fun_prop
       have hx:e 0=Y:=by unfold e heat; change (_+_)*(2*r)= _* (2*r); ring
       exact hx ▸ ((he.tendsto 0).comp hf)
    obtain ⟨t,ht⟩:= eventually_atTop.mp ((((hv.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1/2))).and (hY.eventually (ge_mem_nhds hp))).and (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2*r)))).and (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max (V k i) (V k j))))) -- ge_mem_nhds
    exact ⟨t,fun L h=>⟨(ht _ h).1.1.1,(ht _ h).1.1.2,(ht _ h).1.2,(ht _ h).2⟩⟩
lemma require : ∃ X:ℕ→ℕ→ℝ, ∃ τ:ℕ→ℕ,∀ L:ℕ→Side, (∀ i,τ i≤(L i).val)→Sav G S T Φ X L:=by
    let X k i:= max (2*Tower.χ ((Labels.frames G).level k)) (max (levy G S T Φ k i i+1) (levy G S T Φ k i (i+1)+1))
    have ht(j i k:ℕ)(h:StepStages j i): levy G S T Φ k i j < X k i:=by
       apply lt_of_lt_of_le _ (le_max_right ..); obtain h|h:=stepStages_source h<;> subst j; exact lt_of_lt_of_le (lt_add_one _) (le_max_left ..); exact lt_of_lt_of_le (lt_add_one _) (le_max_right ..)
    choose! τ hτ using fun j i k (h:StepStages j i)=> fuel G S T Φ X i j k (ht j i k h)
    let v j:= (Finset.range (j+1)).sup fun i=> (Finset.range (j+1)).sup (τ j i)
    refine ⟨X,v,fun L h=>⟨fun k i=>le_max_left ..,fun {i j k} ht hp=>?_⟩⟩
    apply hτ j i k ht (L j); refine le_trans ?_ (h j); have hh:k ≤ j:= ((Nat.le_add_right k 3).trans hp).trans ht.1; exact (Finset.le_sup (f:=τ j i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hh))).trans (Finset.le_sup (s:=Finset.range (j+1)) (f:=fun i=> (Finset.range (j+1)).sup (τ j i)) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht.1)))
end YM.FullVolume.Paint.Tower

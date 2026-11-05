import YM.FullVolume.Relay.Cargo
/-
 Log and force rosters in Φ charts. Must earn the wing at every readable
 panel! The heads can't silently change over the tiny probes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t c e t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 430000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q₀"=> A.B.a.budget (m+1)
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I J:Type}[Fintype I][Fintype V][DecidableEq V]
open Luna Frets Empire Imago Luna.Aank Lotus
open FullVolume.Nectar Menu Accent Blush Extra.Histories Planned.GuardedAtom Guard
variable {B:Marker.Census V} (p:Booker A N m n T)(Z:sun→ Booker A N m n T)(o:V→ Site (A.B.a.S.side (m+1) n))
variable (M: Ship p Z o B I)(w:V→ℝ) (hw:∀ i,0<w i)
namespace Ship
-- specializations.
open FullVolume.Nectar Marker
variable (ν:sun→V→ℂ) (u:V→ℝ)
variable (f:sun→ Config G (A.B.a.S.side (m+1) n)→ Poly B) (α:sun→ V → Config G (A.B.a.S.side (m+1) n)→ℂ) (κ:sun→ V→ Res G (A.B.a.S.side (m+1) n))
variable {L:V→ Type}[∀ i,Fintype (L i)](mK : ∀ i:V, Ship p Z o B (L i)) (hO:∀ i,Token p Z o (mK i) (fun s=> α s i) (fun s=> κ s i) (fun s=>ν s i) i (u i))
-- keep in One.S.Serve formula w optional override
abbrev unite : Ship p Z o B ((i:V)× L i):=
   ⟨⟨fun i=> (mK i.1).arm.track i.2,fun i=> (mK i.1).arm.mode i.2,fun i=> (mK i.1).arm.charge i.2,fun i=> (mK i.1).arm.sizes i.2,fun i=> (mK i.1).arm.roots i.2,fun i=> (mK i.1).arm.earns i.2⟩,fun x i=> (mK i.1).crew x i.2,fun i=> (mK i.1).fare i.2,fun x i=>(mK i.1).shares x i.2,fun i=>(mK i.1).earns i.2,fun i=> (mK i.1).unitC _⟩
include hO
local notation "P0"=> unite p Z o mK
lemma tribute (j:V): (P0).slot p Z o j ≤ u j:=by
    unfold slot; rw [Fintype.sum_sigma,sum_eq_single j]; exact (hO j).counted
    · intro i _ hi; exact sum_eq_zero fun a _=> if_neg (fun h=> hi ((B.fire_inj _ _).mp (((hO i).targets _).symm.trans (show (mK i).arm.mode a = _ from h))))
    simp
include hw
lemma tribute_total (e:ℝ)(he:e≤(A.B.a.budget (m+1)).supportExponent): (P0).total p Z o w e ≤ ∑ i:V,w i*u i:=by
    unfold total; rw [Fintype.sum_sigma]; refine sum_le_sum fun i _=> ?_; exact ((mK i).lower_cap p Z o w hw he).trans ((OnlyP.invoice p Z o (mK i) w hw i (hO i).toOnlyP).trans_le (mul_le_mul_of_nonneg_left (hO i).counted (hw _|>.le)))
omit hw
lemma borneE (s:sun)(x:Config G (A.B.a.S.side (m+1) n)): Mach B (ν s)+(P0).allE p Z o s x= Mach B (fun i=>α s i x):=by
    unfold allE; rw [Fintype.sum_sigma]; have he i : (mK i).allE p Z o s x=Poly.send (B.fire i) (α s i x-ν s i):= (hO i).rollE s x
    unfold Mach; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; change _+(mK i).allE p Z o s x=_; rw [he, ← Extra.Trajectories.send_add,add_sub_cancel]
lemma borneK (s:sun)(j:Box (A.B.a.S.side (m+1) n))(x:Config G (A.B.a.S.side (m+1) n)): (P0).allK p Z o s j x= Mach B (fun i=>κ s i j x):=by
    unfold allK; rw [Fintype.sum_sigma]; exact sum_congr rfl (fun i _=> (hO i).rollK s j x)
lemma borneO (s:sun)(j:V)(i:Box (A.B.a.S.side m n))(x:Config G (A.B.a.S.side m n)):(P0).oweK H p Z o s j i x=(mK j).oweK H p Z o s j i x:=by
    unfold oweK; rw [Fintype.sum_sigma, sum_eq_single j]
    · intro i _ hi; exact sum_eq_zero fun a _=> if_neg (fun h=> hi ((B.fire_inj _ _).mp (((hO i).targets a).symm.trans h)))
    simp
variable (a:ℝ) (u':V→ℝ)(hp:0<a)(hu:∀ i,0<u' i)
open ArmadaP
include hp hw hu
lemma combine (he:(A.B.a.budget (m+1)).supportExponent - 4 ≤ e)(h:Attic B (fun s:sun=> (Z s).val.val.val) (A.B.a.budget (m+1)) o w f α κ e v)
     (hF : ((∑ i:V,w i*u i)+4*v) /a + (∑ i:V,(u i)/(u' i)) ≤ 1/8) : ∃ (J:Type) (hx:Fintype J) (U: Ship p Z o B J),
       FoldT p U.arm w a u' (1/8) U.fare ∧ (∀ s:sun, f s=Orchard.story (Z s).val.val.val (ν s) (U.stamp p Z o s))∧∀ s j,(U.oweK H p Z o s j)=(mK j).oweK H p Z o s j:=by
      obtain ⟨E,K,hE,hB,hK⟩:=h.board; let p0:= (A.B.a.budget (m+1)).supportExponent-4
      obtain ⟨I,hI,M,hM,hQ,hU,hX,hS⟩:=stars H p Z o w hw E K (fun i=>(hE i).1) (hB.lower hw he) (hK.lower hw he)
      let P₁:= P0; let Q:= ballast p Z o P₁ M
      refine ⟨_, _,Q, folded p Z o Q w a u' (le_trans ?_ hF),fun s=> ?_,fun s j=>funext fun i=>funext fun y=> ?_⟩
      · apply add_le_add _ (Finset.sum_le_sum fun i _=>div_le_div_of_nonneg_right ?_ (hu _|>.le))
        · unfold Q; rw [paying]; exact div_le_div_of_nonneg_right ((add_le_add (tribute_total p Z o w hw ν u α κ mK hO p0 (by unfold p0; linarith)) hM).trans_eq (by ring)) hp.le
        unfold Q; rw [payingE, hQ,add_zero]; exact tribute p Z o ν u α κ mK hO i
      · rw [(hE s).2]; funext U; unfold restore Orchard.story Accent.play; let x:= (Z s).val.val.val; let A₀ i:=bar x.activities B U i
        have hp(i): A₀ i+Mach B (fun j=>κ s j i U)+K s i U=A₀ i+(Q.allK p Z o s i U):=by unfold Q; rw [sphereK,hX]; unfold P₁; rw [borneK p Z o ν u α κ mK hO]; ring
        have hv:Mach B (ν s)+Q.allE p Z o s U= Mach B (fun i=>α s i U)+∑ i,E s i U:=by unfold Q; rw [sphereE,hU,← add_assoc]; unfold P₁; rw [borneE p Z o ν u α κ mK hO]
        refine congr_arg (fun p'=>(Real.exp (x.exponent U):ℂ) • p') (congr_arg₂ HMul.hMul (congr_arg Poly.pass hv.symm) (congr_arg (fun q=> field q (flags x.p.threshold U)) (funext hp)))
      unfold Q; rw [sphereO,hS,add_zero]; exact borneO H p Z o ν u α κ mK hO s j i y
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.combine

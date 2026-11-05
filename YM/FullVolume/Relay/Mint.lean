import YM.FullVolume.Relay.Hire
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
variable (k:Finset B.Mode)
open ArmadaP
include Z p hw
abbrev VividStamp (F:sun→ I→ Config G (A.B.a.S.side (m+1) n)→ Poly B)(k:Finset B.Mode):=Σ i:I, ↥(VividE (A:=A) (m:=m) (n:=n) F k i)× Bool
variable (hk:k ⊆ lively B)
local notation "Xp"=> VividE (A:=A) (n:=n) (m:=m)
local notation "I_"=> Support S
local notation "B!"=> Box S
include hk
lemma hireLog (E:sun→ Support (A.B.a.S.side (m+1) n)→ Config G (A.B.a.S.side (m+1) n)→ Poly B) (hv:Pact w id E k (A.B.a.budget (m+1)).B e v) (h:∀ s i,Burns o i (E s i) (A.B.a.budget (m+1)).threshold):∃ (I:Type)(i:Fintype I)(M:Ship p Z o B I),
         M.total p Z o w e ≤2*v ∧ (∀ i,M.arm.mode i∈k)∧ (∀ s u,M.allE p Z o s u=∑ i,proposed (E s i u) k) ∧ ∀ s i u,M.allK p Z o s i u=0:=by
    let F:=Xp E k
    have hQ(i:I_)(hh:(F i).Nonempty):∃ j:ℕ,(Wing.logKey j).support p.val.val.val=i ∧∀ y:Booker A N m n T,(Wing.logKey j).blank y.val.val.val:=by
        obtain ⟨z,hz⟩:= hh
        obtain ⟨s,u,hs⟩:= (mem_filter.mp hz).2
        have ht:= (h s i|>.toBorne.place z.val u hs)
        have he: z.val.val.Nonempty:= nonempty_iff_ne_empty.mpr (fun h=> ((lively_ne _).1 (hk z.property)) (Subtype.ext h))
        obtain ⟨j,hj⟩:= (he.image o).mono ht
        let c:=Blush.found j i hj
        refine ⟨c,?_,fun y=>?_⟩
        · change (p.val.val.val.activities.reg c).support=i; rw [show p.val.val.val.activities.reg c =_ from Blush.latch p.val.val.val j i hj p.val.property]
        exact y.val.property.regular _
    let g(i:I_):= if h:(F i).Nonempty then (hQ i h).choose else 0
    have hu i (h:(F i).Nonempty): (Wing.logKey (g i)).support p.val.val.val=i ∧∀ y: Booker A N m n T,(Wing.logKey (g i)).blank y.val.val.val:=by unfold g; rw [dif_pos h]; exact (hQ i h).choose_spec
    let J:=VividStamp (A:=A) (m:=m) (n:=n) E k
    have hf (s i x) (he:E s i x≠0)(hF:(F i).Nonempty): (Wing.logKey (g i)).qualifies ((Z s).val.val.val) x:=by
      have ht: (Wing.logKey (g i)).support ((Z s).val.val.val)=i:= (touched p _ _).symm.trans (hu i hF).1
      change Healthy ((Z s).val.val.val.p.threshold) ((Wing.logKey (g i)).support _) x
      rw [ht,(Z s).val.val.property.1.point]; exact (h s i|>.permits x he)
    obtain ⟨M,hM,hP,hx⟩:=hire p Z o w hw E id (k:=k) (fun i=> .logKey (g i)) hu hf (fun s i=> (h s i).toBorne) hk hv
    have h0(s) (i:J): (M.stamp p Z o s i).M.turn= .logKey (g i.1):= (M.shares s i).trans (hP _).1
    refine ⟨VividStamp (A:=A) (m:=m) (n:=n) E k, inferInstance,M,hM,fun i=>(hP _).2,fun s u=> ?_,fun s i u=>?_⟩
    · have he j:Menu.odour (M.stamp p Z o s j) u=Menu.amount (M.stamp p Z o s j) u:=by rw [Menu.odour,MergeProof.prose,h0 s _,Menu.varnish]
      unfold allE; simp_rw [he]; rw [Fintype.sum_sigma]; exact sum_congr rfl (fun j _=> hx s u j)
    apply sum_eq_zero; intro j _; unfold Menu.fragrance MergeProof.entry; rw [h0]; dsimp only; simp
lemma hireGas (E:sun→ Box (A.B.a.S.side (m+1) n)→ Config G (A.B.a.S.side (m+1) n)→ Poly B) (hv:Pact w Prod.fst E k (A.B.a.budget (m+1)).B e v) (h:∀ s i,Flow o i (E s i) (A.B.a.budget (m+1)).threshold):∃ (I:Type)(i:Fintype I)(M:Ship p Z o B I),
         M.total p Z o w e ≤2*v ∧ (∀ i,M.arm.mode i∈k)∧ (∀ s u,M.allE p Z o s u=0) ∧ ∀ s i u,M.allK p Z o s i u=proposed (E s i u) k:=by
    let F:= Xp E k; let Y:= p.val.val.val; let V₀:=Keeper.sufficient p.val.property
    have hQ(i:B!) (hh:(F i).Nonempty):∃ j:ℕ, barcode Y.activities j=i∧ ∀ u, i.1 ∩ RG.flags (A.B.a.budget (m+1)).threshold u=i.2→ (Wing.gasKey j).qualifies Y u:=by
       obtain ⟨z,hz⟩:=hh; obtain ⟨s,u,hs⟩:= (mem_filter.mp hz).2
       have hh:= h s i|>.permits u (fun h=> hs (by rw [h];rfl)); let t: StockTag (A.B.a.S.side (m+1) n):=⟨i,hh.2⟩
       refine ⟨_,cardK V₀ t,fun u he=> ?_⟩
       have he':(Y.activities.forced (cart V₀ t)).support∩ RG.flags Y.p.threshold u=(Y.activities.forced (cart V₀ t)).inventory:=by
            rw [show Y.p= (A.B.a.budget (m+1)) from p.val.val.property.1.point, show (Y.activities.forced (cart V₀ t)).support=i.1 from congr_arg Prod.fst (cardK V₀ t), show (Y.activities.forced (cart V₀ t)).inventory=i.2 from congr_arg Prod.snd (cardK V₀ t), he]
       exact ⟨he', V₀.pass _ _ he'⟩
    let g(i:B!):= if h:(F i).Nonempty then (hQ i h).choose else 0
    have hu i (h:(F i).Nonempty): barcode Y.activities (g i)=i ∧ ∀ u, i.1 ∩ RG.flags (A.B.a.budget (m+1)).threshold u=i.2→ (Wing.gasKey (g i)).qualifies Y u:=by unfold g; rw [dif_pos h]; exact (hQ i h).choose_spec
    let J:=VividStamp (A:=A) (m:=m) (n:=n) E k
    obtain ⟨M,hM,hP,hx⟩:=hire p Z o w hw E Prod.fst (k:=k) (fun i=> .gasKey (g i)) (fun i h=>⟨congr_arg Prod.fst (hu i h|>.1),fun _=>trivial⟩) (fun s i x he hF=> heart p (Z s) _ x ▸ ((hu i hF).2 x (h s i|>.permits x he).1)) (fun s i=> (h s i).toBorne) hk hv
    have hz(s) (i:J): (M.stamp p Z o s i).M.turn=.gasKey (g i.1):= (M.shares s i).trans (hP i).1
    have hk(s:sun)(i:J): barcode (Z s).val.val.val.activities (g i.1)=i.1:=by unfold barcode;rw [← (boothVal p (Z s)).2]; exact (hu i.1 ⟨_,i.2.1.property⟩).1
    refine ⟨VividStamp (A:=A) (m:=m) (n:=n) E k,inferInstance,M,hM,fun i=>(hP _).2,fun s u=> ?_,fun s i u=>?_⟩
    · apply sum_eq_zero; intro i _; unfold Menu.odour MergeProof.prose;rw [hz]; dsimp only; simp
    have hj(j:J): Menu.fragrance (M.stamp p Z o s j) u i=if j.1=i then Menu.amount (M.stamp p Z o s j) u else 0:=by
        unfold Menu.fragrance MergeProof.entry; rw [hz]; dsimp only; rw [hk s j]; split_ifs
        · exact (Menu.varnish (M.stamp p Z o s j) u).symm
        simp
    unfold allK; simp_rw [hj]; rw [Fintype.sum_sigma,sum_eq_single i]; exact by simpa only [↓reduceIte] using (hx s u i)
    · intro _ _ hn; simp only [hn,↓reduceIte,sum_const_zero]
    simp
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.hireLog
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.hireGas

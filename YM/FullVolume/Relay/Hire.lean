import YM.FullVolume.Relay.Ship
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
-- Vivid entries (activity at any s). By label X:common policy.
def VividE (F:sun→ I→ Config G (A.B.a.S.side (m+1) n)→ Poly B)(k:Finset B.Mode)(i:I) : Finset (↥k) := univ.filter fun j=> ∃ (u:sun) (y:Config G (A.B.a.S.side (m+1) n)), (F u i y).part j.val≠0
-- supply.Assemble.Point masks.
-- use `VividE (A:=A)` etc (Stage vs only shape.Side determined by elaborator)
variable {k:Finset B.Mode}(F:sun→ I→ Config G (A.B.a.S.side (m+1) n)→ Poly B) (X:I→ Support (A.B.a.S.side (m+1) n))
local notation "Y_"=>VividE (A:=A) (n:=n) (m:=m) F k
local notation "Z₀"=> (fun s:sun=> (Z s).val.val.val)
abbrev proposed (a:Poly B)(s:Finset B.Mode) : Poly B:=∑ i∈s,Poly.send i (a.part i)
variable (k)
open ArmadaP
include Z F p hw
local notation "Vv"=> Σ i:I,(↑(Y_ i)) × Bool
-- picks g(i) Wing only needed for used columns
lemma hire (g:I→Wing) (he : ∀ i, (VividE (A:=A) (m:=m) (n:=n) F k i).Nonempty→ (g i).support p.val.val.val=X i ∧∀ p': Booker A N m n T, (g i).blank p'.val.val.val) (hv:∀ s i x,F s i x≠0→(VividE (A:=A) (m:=m) (n:=n) F k i).Nonempty→(g i).qualifies (Z s).val.val.val x)
    (hH:∀ s i,Borne o (X i) (F s i) ((A.B.a.budget (m+1)).threshold)) (hk:k ⊆ lively B)
    (hp:Pact w X F k (A.B.a.budget (m+1)).B e v):∃ M: Ship p Z o B (Σ i:I, ↑(VividE (A:=A) (m:=m) (n:=n) F k i) × Bool),
        M.total p Z o w e ≤2*v ∧ (∀ i, M.arm.track i=g i.1 ∧ M.arm.mode i ∈ k) ∧∀ s u i,(∑ j:↑(VividE (A:=A) (m:=m) (n:=n) F k i) × Bool, Menu.amount (M.stamp p Z o s ⟨i,j⟩) u)=proposed (F s i u) k:=by
    let Q(i:I):= VividE (A:=A) (m:=m) (n:=n) F k i; let Y:=Σ i:I, ↑(Q i) × Bool
    have hQ(i): ∀ x:↑(Q i),∃ s u,(F s i u).part x.val.val ≠ 0:= fun x=> (mem_filter.mp x.property).2
    have hP(i):∀ x:↑(Q i), (g i).support p.val.val.val=X i∧∀ p':Booker A N m n T,(g i).blank p'.val.val.val:=fun x=> he i ⟨_,x.property⟩
    let T (i:Y):= i.2.1.val.val
    have hi(i:Y): (T i).val.Nonempty:= nonempty_iff_ne_empty.mpr (fun hp=> ((lively_ne _).1 (hk i.2.1.val.property)) (Subtype.ext hp))
    let U: ArmadaP A N m n _ p o B Y:= {
                                           track:=fun i:Y=> g i.1
                                           mode:=T
                                           charge:=fun i=> Matric.prizes i.2.2
                                           sizes:=hi
                                           roots:=fun i=> ?_
                                           earns:=fun i=> (hP _ i.2.1).2 }
    case refine_1=> rename_i i; obtain ⟨s,u,ha⟩:= hQ _ i.2.1; rw [(hP _ i.2.1).1]; exact (hH s i.1).place _ _ ha
    obtain ⟨b,hb,h⟩:=hp.coins
    let X₀ (i:Y)(s:sun)(x:Config G (A.B.a.S.side (m+1) n)):ℝ:=Matric.sides i.2.2 ((F s i.1 x).part (T i))
    let q (i:Y):= b (i.1,i.2.1.val)
    have hh(i:Y):Feel (X₀ i) (q i):=by
         have H:=Feel.transit (Matric.sides i.2.2) (id (α:= Config G (A.B.a.S.side (m+1) n))) (h (i.1,i.2.1.val)) (fun x=> (Matric.sidePrice i.2.2 _).trans_eq (one_mul _).symm) zero_le_one
         rw [one_mul] at H; exact H
    have hx i s: ((g (i:Y).1).support ((Z s).val.val.val))=X i.1:= (touched p (Z s) _).symm.trans (hP _ i.2.1).1
    let M(s:sun)(i:Y): Lotus.Leaf (Z s).val.val.val:= {
         turn:=g i.1
         weight:=q i
         ingredient:=X₀ i s
         earn:=fun x=>(hh i).worth s x
         scopedR:=by rw [hx i s,(Z s).val.val.property.1.point]; exact fun _ _ ha hp=>congr_arg (fun z:Poly B=> Matric.sides i.2.2 (z.part (T i))) ((hH s _).home _ _ ha hp)
         blank:=(hP _ i.2.1).2 (Z s)
         grant:=fun x h=>hv _ _ _ (fun ht=> h (by unfold X₀; rw [ht,Poly.part_nil,map_zero])) ⟨_,i.2.1.property⟩
         glows:=fun t₁ U=>congr_arg (fun z:Poly B=>Matric.sides i.2.2 (z.part (T i))) ((hH ..).turns t₁ U)
         borel:=(Matric.sides _).continuous.measurable.comp ((hH ..).me _) }
    let L: Ship p Z o B Y:= ⟨U,M,q,fun _ _=>rfl, hh, fun _=> Matric.prizes_one _⟩
    refine ⟨L,?_ ,fun i=> ⟨rfl,i.2.1.val.property⟩,fun s u i=>?_⟩
    · apply le_trans _ (mul_le_mul_of_nonneg_left hb zero_le_two)
      unfold total; rw [Fintype.sum_sigma,Fintype.sum_prod_type (α₁:=I),mul_sum]; apply sum_le_sum; intro i _; rw [Fintype.sum_prod_type];
      have hc (x:↑(Y_ i))(j:Bool): (L.arm.track ⟨i,x,j⟩).support p.val.val.val=X i:= (hP _ x).1
      simp_rw [Fintype.sum_bool,hc];
      let t (j:↑k):=Poly.toll w j.val*b (i,j)
      let f(j:↑k):= Real.exp (e*coverNumber (Q₀).B (X i))*Poly.toll w j.val*b (i,j)
      have ht(j):0≤ f j:=mul_nonneg (mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le) (h _|>.positives)
      change ∑ j:↑(Y_ i), (f j.val + f j.val)≤ 2*∑ j:↥k,f j
      simp_rw [← two_mul,← Finset.mul_sum, Finset.sum_coe_sort]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> ht i)) zero_le_two

    rw [Fintype.sum_prod_type]; have hu (i:I)(x:↑(Q i)): (∑ j:Bool, Menu.amount (L.stamp p Z o s ⟨i,(x,j)⟩) u)=Poly.send x.val.val ((F s i u).part x.val.val):=by
           rw [Fintype.sum_bool]; simp_rw [Menu.varnish]; unfold L M T
           let a:= (F s i u).part x.val.val
           change Poly.send _ ((a.re :ℂ)*1)+Poly.send _ ((a.im:ℂ)*Complex.I)= Poly.send _ a
           rw [← Extra.Trajectories.send_add,mul_one]; exact congr_arg _ (Complex.re_add_im _)
    rw [Finset.sum_congr rfl (fun j _=>hu i j)]
    unfold proposed; change (∑ j:↑(Q i),Poly.send j.val.val ((F s i u).part j.val.val))=_; rw [sum_coe_sort (Q i) (fun j=>Poly.send j.val ((F s i u).part j.val)),← Finset.sum_coe_sort k (fun j=>Poly.send j ((F s i u).part j))]
    refine sum_subset (subset_univ _) fun j _ hv=> ?_; rw [show (F s i u).part j.val=0 from of_not_not (fun h=> hv (mem_filter.mpr ⟨mem_univ _,s,u,h⟩)), Poly.send_zero]
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil

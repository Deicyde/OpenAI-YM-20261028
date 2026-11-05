import YM.FullVolume.Spiral.Bale
import YM.FullVolume.Spiral.Chrome
import YM.FullVolume.Gables.Major
/- exact top Voice line and angular cut.Capture. Fixed gaskets and passports.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Bale
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna Tower
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn Extra.Histories.Attach
open UniformSpace FullVolume.Amp
open Beam PaidBeam
variable {R R':Rep G n}
open Progress.DirectedRecipe
variable {R:sun→Rep G n}(X:Desk G n)(V:∀ i:sun, Along X.orient (R i))(hX:HasSlots X.orient.p X.orient.activities)(hV:∀ i:sun,HasSlots (R i).p (R i).activities)
variable (A:SectionData F)(x:F.Coeff)(Y:Hol G)(hS:A.Sound Y)
local notation "H!"=> X.orient
local notation "k₀"=> X.k
set_option quotPrecheck false
local notation "Θ"=> ((A).footprint (0:Site n))
local notation "χ"=> X.orient.activities.forced
local notation "S!"=> fun s=> TopY F A (R s) (hV s) i x
variable {z:ℕ→ℝ} (ht: ∀ v:Site n, SumBudget (fun k=> if v∈(X.orient.activities.forced k).support then X.orient.p.mass (X.orient.activities.forced k).support (z k) else 0) (X.k^2))
variable (hp:∀ i U,PaidBeam (fun s:sun=>(R s).activities.K i U) (z i))
variable {hp0:ℝ}(he: fee F X.orient.p (A.footprint (0:Site n)) hp0 (X.k^2) ≤ X.k)(hh:1 ≤ hp0) (hr:∀ (j:F.Index) (U:Config G n),‖A.places (Size.axis F j) 0 U‖ ≤ hp0)
set_option quotPrecheck false
local notation "jℓ"=> F.coeffSize (F.core x)
local notation "β!"=> fullCost F (H!).p hp0
local notation "b!"=> (β!*jℓ)
-- sum authorization.Price.F.Rate certificate. actually charge ≤ Fee k.P.Sem even at ARC 2.
include V hX hV ht hp hS he hh hr
local notation "h'"=> badge Θ i hX
local notation "J_"=> Attach.Cluster (H!) Θ
lemma puffs :∃ a:ℕ→ℝ,SumBudget (fun i=>X.orient.p.mass (X.orient.activities.forced i).support (a i)) (X.k*F.coeffSize (F.core x))∧∀ k U,PaidBeam (fun t:sun=>(TopY F A (R t) (hV t) i x).forced k U) (a k):=by
    let f(q:J_):ℝ:= b!*(∏ i∈q.val,z i); let h:= badge Θ i hX; let a:= Function.extend h f 0; have hq(q): a (h q)= f q:=h.injective.extend_apply ..
    let p(k:ℕ):=Push.Local.patch X.orient.activities k; let S:=A.footprint (0:Site n)
    have h0 i:0≤ z i:= PaidBeam.price (hp i (1:Config G n)); have hC :0 ≤ b!:= by have h:= supplement_bound A X.orient 0 hS hh hr x (1:Config G n);exact (norm_nonneg _).trans h
    have hx0: SumBudget (fun i=>X.orient.p.mass (p (h i)) (a (h i))) (X.k*F.coeffSize (F.core x)):=by
       have hz(p:J_): (X.orient.activities.forced (h p)).support=Attach.span X.orient Θ p:=badge_geom ..
       unfold p Push.Local.patch; simp_rw [hq,hz,f,Extra.Histories.mass_scale]; apply Push.AbsoluteSums.budget_loosen (Extra.Histories.budget_scale (Attach.budget_cluster X.orient Θ h0 ht) hC)
       exact Eq.trans_le (b:=(fee F X.orient.p Θ hp0 (X.k^2)*jℓ)) (by unfold Extra.Histories.fee; ring) (mul_le_mul_of_nonneg_right he (Work.G08.size_nonneg ..))
    refine ⟨a,Local.sumBudget_pass h _ hx0 (fun i hi=> ?_),fun k U=>?_⟩
    · rw [show a i=0 from Function.extend_apply' _ _ _ hi,BudgetPoint.mass,mul_zero]
    by_cases hA: k∈ Set.range h
    · obtain ⟨q,rfl⟩:= hA
      rw [hq]; choose u hu using fun i=> there (V i) q
      let y:= fun s:sun=> (TopY F A (R s) (hV s) i x).forced (h q) U
      have ht' (s:sun): y s = if Attach.span X.orient Θ q ∩ flags X.orient.p.threshold U= Attach.debts X.orient Θ q then supplement A X.orient 0 x U * ∏ i∈q.val,((R s).activities.K i U:ℂ) else 0:=by
         unfold y; rw [show h q= _ from numbering (V s) q (u s) (hu s) hX (hV s) i, tube2]
         have hl: supplement A X.orient (0:Site n)= supplement A (R s) 0:=by funext v U; simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk,(V s).price]
         obtain ⟨hP,hQ⟩:= markings (V s) q (u s) (hu s)
         rw [hP,hQ, (V s).price,hl,← hu s]; rfl
      change PaidBeam y (f q); rw [funext ht']; split
      next hz=> exact strum ((PaidBeam.static _ |>.larger (supplement_bound _ _ _ hS hh hr x U))) (funds _ _ z (fun i=> tint (hp i U)))
      next hz=>apply (PaidBeam.static (0:ℂ)).larger; rw [norm_zero]; exact mul_nonneg hC (prod_nonneg fun i _=>h0 i)
    rw [show a k=0 from Function.extend_apply' _ _ _ hA]; have hz (s:sun):(TopY F A (R s) (hV s) i x).forced k=0 :=by
       apply blank1
       rintro ⟨q,he⟩
       obtain ⟨c,hc⟩:= there (V s).sym q; exact hA ⟨c,(numbering (V s).sym q c hc (hV s) hX i).symm.trans he⟩
    simp_rw [hz,Pi.zero_apply]; simpa using PaidBeam.static (0:ℂ)
-- Z weave support singleton.Criterion.Format linear. from every real hS.Birth.Tune with same S.Work; arbitrary q only at t.
variable (hT:∀ t:sun, (TopY F A (R t) (hV t) i x).Format 0 Y X.orient)
include hT
local notation "Δ!"=> Muse.verso
lemma born_arc : Forum (fun s:sun=> TopY F A (R (Muse.verso s)) (hV (Muse.verso s)) i x) 2 x Y X 0 (F.coeffSize (F.core x)):=by
    let T (s:sun):= TopY F A (R (Δ! s)) (hV (Δ! s)) i x; refine ⟨fun _=>rfl,one_le_two,fun w u h=>?_,fun w u h=>?_⟩
    · change F.coeffSize (Jams.mix w (fun _=> x-x))≤ _; simp [Jams.mix,Frame.coeffSize]
    obtain ⟨a,hA,hB⟩:=puffs X V hX hV A x Y hS ht hp he hh hr
    let v:= weave w T; change v.Format 0 Y X.orient ∧ v.remBound ..
    let Q: ℕ→ Config G n→ℂ :=v.forced; have hz:v.regular=0:=by
        change Jams.mix w (fun _=> (0:ℕ→ Config G n→ℂ))=0; simp [Jams.mix]
    have ht0: v.support= fun _=>{(0:Site n)}:= rfl
    have hm t: ForceFormat (X.orient).p (X.orient).activities 0 (T t).forced:=let h:=hT (Δ! t); ⟨h.forcing,h.carried,h.invariant,h.supported,h.borel⟩
    have hh : ForceFormat (X.orient).p X.orient.activities 0 v.forced:=by
       let f(i:sun):=w i • (T i).forced
       have hp1(s:Finset sun): ForceFormat (X.orient).p X.orient.activities 0 (∑ i∈s,f i):=by
            induction s using Finset.induction_on with
            | empty=>rw [sum_empty]; have hx:=primary_format (H:=Y) (R:=X.orient) (o:=0) (0:F.Coeff); exact ⟨hx.forcing,hx.carried,hx.invariant,hx.supported,hx.borel⟩
            | insert i s hi ih=>
                 rw [sum_insert hi]; have hA:f i=(Extra.Histories.stretch (w i:ℂ) (T i)).forced:=funext fun k=> saneF (s:= w i) (x:=(T i).forced k)
                 rw [hA]; have ht:= stretch_format (w i:ℂ) (hT (Δ! i)); exact ForceFormat.add ⟨ht.forcing,ht.carried,ht.invariant,ht.supported,ht.borel⟩ ih
       exact hp1 w.support
    constructor
    · refine ⟨fun i=>?_,fun i=>Finset.mem_singleton_self _,fun i=>?_,fun i he=> ?_,hh.forcing,hh.carried,hh.invariant,hh.supported,hh.borel⟩<;> rw [hz]
      · exact ((primary_format (H:=Y) (R:=X.orient) (o:=0) x).smooth _)
      · rfl
      exact (primary_format (H:=Y) (R:=X.orient) (o:=0) x).projects _ he
    have h0 := Jams.stripe_pos h
    refine ⟨0,_,le_rfl,mul_nonneg h0 (Work.G08.size_nonneg _ _),(zero_add _).le,X.sane,⟨0,budget0 ..,fun i=>?_⟩,fun i=>u*a i,?_ ,fun i=>⟨mul_nonneg h0 (PaidBeam.price (hB i 1)),fun U=>?_⟩⟩
    · rw [hz]; exact (regular0 ..).2
    · simp_rw [Extra.Histories.mass_scale, mul_left_comm X.k]; exact Extra.Histories.budget_scale hA h0
    change ‖Jams.mix w (fun i=>(T i).forced) i U‖ ≤ _; rw [mix_apply',mix_apply']; exact Jams.mix_d _ h (Muse.arc2 (hB i U))
lemma atrophy : PaidBeam (fun s:sun=> Tower.press Y (TopY F A (R (Muse.verso s)) (hV (Muse.verso s)) i x) (Keeper.sufficient hX)) (2* F.coeffSize (F.core x)):=by
    let F1(s:sun):= TopY _ A (R (Muse.verso s)) (hV _) i x; let f(i:sun):= Tower.press Y (F1 i) (Keeper.sufficient hX); have hq:=Forum.compass (Keeper.sufficient hX) (born_arc X V hX hV A x Y hS ht hp he hh hr hT)|>.1
    have ht:Scout 1 (phraseS f) (2*jℓ):=(hq.recovery (a:=1) le_rfl one_lt_two).enlarged (le_of_eq (by ring)) -- binder
    obtain ⟨w,hw,h⟩:=ht.scored; let v:Beam (Completion (Matric.Coin F Y X)):=⟨w,memℓp_gen (by simpa using hw.2.1)⟩ -- F shadow rename
    refine ⟨v,(paid v|>.tsum_eq.symm).trans_le hw.2.2,fun i=>?_⟩
    have hx:=h i.val i.2; simp_rw [div_one] at hx; rw [Jams.phrased] at hx; exact hx.tsum_eq.symm
end YM.FullVolume.Paint.Bale

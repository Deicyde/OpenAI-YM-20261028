import YM.MergeProof.Emit
import YM.MergeProof.Jetty
import YM.MergeProof.Limb
import YM.MergeProof.Record

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A rA K dk ex y')
open MergeProof Accent Set GridApprox.Nil
variable (b':V→Site c)(hw:∀ i,GridApprox.Nil.Scoped (A:= {x| b' x∈ (M i).crest.image S.ratio.parent}) (z i)) (rV:V→ℝ)(hV:∀ i,0<rV i)(hx:∀ i, Poly.price rV (z i) ≤ 1) (ho:∀ i,(z i).part B.quiet=0)
include h
local notation "T0"=> Photo.tones M Y χ rA
def headSheet (p:Y.fragrances)(U: Config G c):=Switch.sound z (Photo.tones M Y χ rA p U)
def Fleece (p:ℕ)(U: Config G c): Poly B:= Switch.sound z (fun t j=> K t j p U)
include hV hx
lemma flag_E : Towed rV (fun i:Y.fragrances=>Y.bookFoot (.inr i)) (headSheet M Y χ rA B z) A.p.B dk ex:=by
   obtain ⟨u,hp,hF,hQ⟩:=h.exponent; exact ⟨u,hF,hQ,fun i=> crystal (hp i) hV hx⟩
omit h in
lemma flag_K {P:BudgetPoint} (hA : Pays A.activities P K ex dk)(he:0≤ dk) : Towed rV (fun i=>(A.activities.forced i).support) (Fleece K B z) P.B dk ex:=by
   obtain ⟨u,hp,hF⟩:=hA.bought; have hu:= Product.everyone_ne _ _ (fun i=> (hp i).rocket) (fun i _=> (A.activities.forced i).inventory_ne.mono (A.activities.forced i).inventory_sup) hF; have he' : Summable u:= hu.2.1.of_nonneg_of_le (fun i=> (hp i).rocket) (fun i=> le_mul_of_one_le_right (hp i |>.rocket) (Real.one_le_exp (mul_nonneg he (Nat.cast_nonneg _)))); exact ⟨u,he',hF,fun i=> crystal (hp i) hV hx⟩
omit hV hx
variable [Fintype V]
include hw ho
lemma curtain (p:Y.fragrances): Burns b' (Y.bookFoot (.inr p)) (headSheet M Y χ rA B z p) A.p.threshold:= by
   obtain ⟨u,hp,hF,hQ⟩:=h.exponent; let t:= Photo.tones M Y χ rA; let c:= Pressure.temp x; let X:= Y.bookFoot (.inr p); let u:= t p
   have ht(v q) : UsesFinal c X (fun U=>u U v q) ∧ Measurable (fun U=>u U v q) ∧ GaugeInvariant (fun U=>u U v q) ∧ ∀ U,u U v q≠0→Healthy c X U:=by
      obtain ⟨he,hb,hz,hx⟩:= Palette.permits M Y χ rA p q v; obtain ⟨hh,hy,hJ,hU⟩:=Palette.permits M Y χ rA p ∅ 0
      exact ⟨fun U V hv ht=>congr_arg₂ (·-·) (he _ _ hv ht) (hh _ _ hv ht),hb.sub hy,fun g V=>congr_arg₂ (·-·) (hz g V) (hJ g V),fun V hv=>of_not_not fun ht=> hv ((congr_arg₂ (·-·) (not_not.mp (mt (hx _) ht)) (not_not.mp (mt (hU _) ht))).trans (sub_self ..))⟩
   let H(i:Finset ι)(V):= jet (u V) i
   rw [h.temp]
   refine {toBorne:= bear (u:=u) (fun i=>?_),sil:=fun V=> (sunset _ (hp p) z _ ho).trans ?_, permits:=fun U hu=> freight (u:=u) U ?_ hu }
   · -- scope support
     refine ⟨fun V U hv hh=>congr_arg (fun f=>jet f i) (funext fun t=>funext fun p=>(ht t p).1 V U hv hh),fun g V=>congr_arg (fun f=>jet f i) (funext fun t=>funext fun p=>(ht t p).2.2.1 g V),Paid.jet_meas (hp _) (fun x _ p=>(ht x p).2.1) _,fun V hv j hj=>?_⟩
     have hP:(M j).crest.image S.ratio.parent ⊆ X:=by intro U hu; by_contra hU; exact hv (jet_erase ((hp p|>.works V).choose_spec) (fun t _ q =>congr_arg (·-_) (Palette.limps M Y χ rA V j U hu p hU t q)) i hj)
     exact fun m hm=>hw j _ (fun ht=>hm (ht.trans fun i hi=>hP hi))
   · intro k hv; by_contra hn; apply hv
     have hh : Models (u U) 0 :=⟨fun x hx=>funext fun i=> (show value x (0:Score ι) i=0 from by simp [Switch.value]).trans (not_not.mp (mt ((ht x i).2.2.2 U) hn)).symm,fun j=> tendsto_const_nhds⟩ -- edit
     rw [hh.exact]; rfl
   simp [Photo.tones]
omit ho in
lemma river (i:ℕ): Flow b' (barcode A.activities i) (Fleece K B z i) A.p.threshold:=by
   have ht:= fun j=> h.gas.rear i j; let X:= barcode A.activities i; let u:= fun U t j=> K t j i U
   obtain ⟨c,hp,hF⟩:=h.gas.bought
   refine { toBorne:=bear (u:=u) (fun s=>?_)
            permits:=fun U hu=>?_ }
   · refine ⟨(ht s).1,(ht s).2.2.1,(ht s).2.1,fun U hu j hj=>?_⟩
     have hP:(M j).crest.image S.ratio.parent ⊆ X.1:=by
        intro V hv; by_contra hh; exact hu (jet_erase ((hp i|>.works U).choose_spec) (fun t _ q =>congr_fun (h.reacts V j hv i t q hh) U) s hj)
     exact fun m hm=>hw j _ (fun ht=>hm (ht.trans fun i hi=>hP hi))
   exact ⟨freight (u:=u) U (fun p hx=> ((ht p).2.2.2 _ hx).1) hu,(A.activities.forced i).inventory_ne,(A.activities.forced i).inventory_sup⟩
end YM.Merge.Photo

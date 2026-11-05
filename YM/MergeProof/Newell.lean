import YM.MergeProof.Bungalow
import YM.MergeProof.Wicket

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I Y : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{n: Side} {e f t u v:ℝ}{r:V→ℝ}
-- numerator pays *named* marker per mode INCLUDING root allocations at terminal. 
lemma harvest [Fintype I]{F:I→Y→Poly B}{S:I→Support n}{M:ℕ}(ht:Towed r S F M e f)(hr:∀ i,0< r i)(he:0≤e)(x:Y){J:Type} [Fintype J] (o:J→Site n)(hip:∀ i,F i x ≠ 0 →∃ j,o j ∈ S i): ∑ i,Poly.price r (F i x) ≤ Fintype.card J*f := by
    obtain ⟨g,hg,hq,hB⟩:=ht
    let s (j:J)(i:I):= if o j∈S i then g i*Real.exp (e*coverNumber M (S i)) else 0
    have hp j i : 0≤ s j i:= hq (o j)|>.1 i -- decidability
    calc
       _ ≤ ∑ i:I,∑ j:J,s j i:= Finset.sum_le_sum (fun i _=>by
             by_cases hi:F i x=0
             · rw [hi,Poly.zero_price]; exact Finset.sum_nonneg fun i' _=>hp ..
             obtain ⟨j,hj⟩:=hip i hi;have he':= (hB i).fares hr
             have hy:g i≤ s j i :=by unfold s; rw [if_pos hj]; exact le_mul_of_one_le_right he'.1 (Real.one_le_exp (by positivity))
             exact (he'.2 x).trans (hy.trans (Finset.single_le_sum (f:=fun j=> s j i) (fun i _=> hp ..) (Finset.mem_univ j))))
       _ ≤ ∑ _ : J, f:= by
          rw [Finset.sum_comm]; refine Finset.sum_le_sum (fun i _=>?_)
          have he': (∑' j,s i j)≤f:= hq (o i)|>.2.2; rwa [tsum_fintype] at he'
       _=_:=by simp
lemma grid_pay (F : Box n→Poly B)(P:Support n)(hr:∀ i,0<r i): Poly.price r (field F P) ≤ Real.exp (∑ i, Poly.price r (F i)):=by
   let X:=Box n; let A(i:X):= Poly.price r (F i)
   have ha i: 0≤A i:= Poly.nonnegative hr _
   unfold field; apply (Poly.batch hr ..).trans; calc
    _ ≤ ∑ i:Finset X, ∏ j∈i,A j:= Finset.sum_le_sum (fun i _=> by unfold grid;split; exact Poly.multiple hr i F;next=>rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _=>ha i)
    _ = ∏ i:X, (1+A i) := by rw [Finset.prod_one_add,Finset.powerset_univ]
    _ ≤ _:= by rw [Real.exp_sum]; exact Finset.prod_le_prod (fun i _=> add_nonneg zero_le_one (ha i)) (fun i _=> le_trans (le_of_eq (add_comm ..)) (Real.add_one_le_exp _))
structure Vault (r : V→ℝ) (F:V→ Config G n→ℂ)(g:V→Box n→ Config G n→ℂ)(x y : ℝ):Prop where
   exp i U:r i*‖F i U‖≤ x
   forces i U:∑ j,r i*‖g i j U‖≤y
variable {A : Rep G n}{F:V→ Config G n→ℂ}{g:V→Box n→ Config G n→ℂ}{X: Config G n→Poly B}{o:V→Site n}{a x y l Λ σ C:ℝ}
local notation "P!"=> A.p
lemma touchdown {S:Support n} {f:Config G n→Poly B} (h:Borne o S f t)(U) (hp:f U≠0) (ht:rises (f U)): ∃ j,o j∈ S:=by
   obtain ⟨i,hi⟩:∃ i,(f U).part i ≠ 0:=by by_contra! hQ; apply hp; ext i; rw [hQ]; rfl
   obtain ⟨j,hj⟩:= Finset.card_pos.mp (Nat.lt_of_lt_of_le (by decide:0<2) (ht i hi)); exact ⟨j,h.place i U hi (mem_image_of_mem o hj)⟩
lemma steer (hr:∀ i,0<r i)(hx:Served A F g X o r e f)(h:A.activities.Valid A.p t u) (hv:Vault r F g x y) (he:0 ≤ e) (U) : Poly.price r (X U) ≤ Real.exp (A.exponent U+Fintype.card V*(x+y+2*f)+Fintype.card (Site n)*u) :=by
   obtain ⟨H,K,hH,hc,hK,rfl⟩:= hx; let a:ℝ:= Fintype.card V; let s:ℝ:=Fintype.card (Site n)
   let J:=Mach B (fun i=> F i U)+ ∑ i,H i U; let T (p):= bar A.activities B U p+Mach B (fun i=> g i p U)+K p U
   have hg' : ∑ i,Poly.price r (bar A.activities B U i)≤ s*u:=by
      apply harvest (Y:=Config G n) (F:=fun i U=>bar A.activities B U i) (J:=Site n) (vacant A.activities _ B h r hr) hr A.p.exponent_pos.le U id; intro i hi
      have ht:= (granular A.activities _ B (o:=o) h i).permits U hi; obtain ⟨j,hj⟩:=ht.2.1.mono ht.2.2; exact ⟨j,hj⟩
   have hv' := harvest hK hr he U o fun i hi=> touchdown (hH.flag i|>.1.toBorne) U hi ((hH.flag i).2 U)
   have hd: Poly.price r J≤a*(x+f):=by
      have hx:= harvest hc hr he U o fun i hi=> touchdown (hH.exp i|>.1.toBorne) U hi ((hH.exp i).2 U)
      rw [mul_add]; refine (Poly.addition hr ..).trans (add_le_add ((Poly.batch hr ..).trans ?_) ((Poly.batch hr ..).trans hx))
      · simp_rw [Poly.solo,Poly.solo_toll]; apply le_trans (Finset.sum_le_sum (fun i _=>hv.exp i U)); simp [a] -- Goals
   have hP: ∑ i,Poly.price r (T i) ≤ s*u+a*y+a*f:=by
      have h1 : ∑ i:Box n,Poly.price r (Mach B (fun j=>g j i U)) ≤ a*y:=by
           apply le_trans (Finset.sum_le_sum (fun i _=> Poly.batch hr ..))
           simp_rw [Poly.solo,Poly.solo_toll]; rw [sum_comm]; apply le_trans (Finset.sum_le_sum (fun i _=>hv.forces i U)); simp [a]
      apply le_trans (Finset.sum_le_sum (fun i (_:i∈(univ:Finset (Box n)))=>poly _ _ _)) -- replace
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]; exact add_le_add (add_le_add hg' h1) hv'
   change Poly.price r ((Real.exp (A.exponent U):ℂ) • (Poly.pass J * _)) ≤ Real.exp (_ + a*_+s*u)
   rw [Poly.adapted,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
   refine mul_le_mul_of_nonneg_left (Poly.multiplication hr (Poly.pass J) (field T (flags A.p.threshold U))) (Real.exp_pos _).le |>.trans ((mul_le_mul_of_nonneg_left (mul_le_mul ((Poly.pass_budget hr _).trans (Real.exp_monotone hd)) ((grid_pay T (flags A.p.threshold U) hr).trans (Real.exp_monotone hP)) (Poly.nonnegative hr _) (Real.exp_pos _).le) (Real.exp_pos _).le).trans_eq ?_)
   rw [← Real.exp_add _ (s*u+a*y+a*f),← Real.exp_add]; congr 1; ring
where
 poly (p q v:Poly B): Poly.price r (p+q+v)≤ Poly.price r p+Poly.price r q+Poly.price r v:= (Poly.addition hr ..).trans (add_le_add_left (Poly.addition hr ..) _)
end YM.MergeProof.Accent

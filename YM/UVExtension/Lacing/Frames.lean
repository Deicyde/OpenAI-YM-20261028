import YM.UVExtension.Lacing.Bridge
/-! # analytic operator grammar. quantitative per entry, α absorption
 vintage real cases derive.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing.RoutesF
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet InputColumn Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {n n':Side} {d :ℕ} {F:Frame G d} {H: Hol G} {p P : BudgetPoint} {ι:Type}
variable (L:RoutesF F n n' p P H)
local notation "Bc" => Cow G n' p d H
local notation "Lc" => Bucket F P H n
set_option quotPrecheck false
local notation "tc"=>turnCost P.order P.power

set_option synthInstance.maxHeartbeats 80000
variable {L}{u v q w : ℝ}{r:Side}{T:Heading F} (m:Motion) (b:Cow G n' p d H) (hn:2 ≤ n.val)
local notation "sCap"=> Eyelet.cap n F H P m hn
namespace Tips
-- derive actual Estimates.H.
lemma clips (t:Lc) {u} (h: tc * ‖t.2.1‖≤ u) (he:‖t.2.2‖ ≤ u): ‖(Eyelet.cap n F H P m hn t).2‖ ≤ u := by
    exact max_le (((rungE (d:=d) m H P hn).choose_spec.2 t.2.1).trans h) (((rungK m G P n).choose_spec.2 t.2.2).trans (le_trans (one_mul ..|>.le) he))
lemma deal (w: Lc)(q:ℕ↪ℕ) : ‖(rooms n F H P q w).2‖ ≤ ‖w.2‖:= max_le_max (duck d H P q _) le_rfl
lemma strum (h: Tips L r T u v)(i:F.Index) : let x:= Size.axis F i; let X:= L.rain b (some i)
    F.coeffSize ((Eyelet.cap n F H P m hn X).1- Motion.patch F m (T.leads r x)) ≤ u * F.coeffSize (F.core x)+ (2*u)*‖b‖∧
      ‖(Eyelet.cap n F H P m hn X).2‖ ≤ v*F.coeffSize (vowel F r (F.core x)) + (2*u)*‖b‖ := by
   intro x X
   let t:= rooms n F H P (aisleN (code Listing) (.inl ())) (L.vane (some i)); let M':=L.vane (some i); let D':= vowel F r (F.core x)
   have hP: X=t+L.Pillow b:= Counts.rains h.counts b _
   have hz:=h.speed i
   have hx : F.coeffSize ((sCap X).1-Motion.patch F m (T.leads r x))≤ orbitCost F *F.coeffSize (X.1-T.leads r x):= by rw [show (sCap X).1 - Motion.patch F m (T.leads r x) = Motion.patch F m (X.1 - T.leads r x) from (Planned.GuardedAtom.patch_sub m ..).symm]; exact patch_cost F m _
   rw [hP,Prod.fst_add,show t.1=M'.1 from rfl] at hx
   refine ⟨?_,?_⟩
   · rw [show M'.1+(L.Pillow b).1-T.leads r x=M'.1-T.leads r x+(L.Pillow b).1 by abel] at hx
     rw [hP]; apply hx.trans; apply (mul_le_mul_of_nonneg_left (Size.add F _ _) (zero_le_one.trans (orbitCost_one_le F))).trans; rw [mul_add]; exact add_le_add hz.1 (h.counts.altX b)
   let s:=v*F.coeffSize D'
   have hWi :‖t.2.1‖ ≤ ‖M'.2.1‖:= duck ..
   have hw :‖(sCap t).2‖ ≤ s:= clips m hn t ((mul_le_mul_of_nonneg_left hWi (zero_le_one.trans (turnCost_near _))).trans hz.2.1) hz.2.2
   rw [hP,map_add,Prod.snd_add]; have ht:=h.counts.altW b; exact (norm_add_le ..).trans (add_le_add hw (clips m hn _ ht.1 ht.2))
lemma shifts (h: Tips L r T u v)(i:Option F.Index)(x y:Bc) : let a:= sCap (L.rain x i) - sCap (L.rain y i)
    let c:=2*u*‖x-y‖; F.coeffSize a.1 ≤ c ∧ ‖a.2‖ ≤ c:=by
   intro a c; have hx:a= sCap (L.Pillow (x-y)):= by
      unfold a; rw [h.counts.rains x,h.counts.rains y,← map_sub,add_sub_add_left_eq_sub]
      change sCap (h.counts.caravan x - h.counts.caravan y)=sCap (h.counts.caravan (x-y)); rw [map_sub h.counts.caravan x y]
   have hv:= h.counts.altW (x-y); rw [hx]; exact ⟨(patch_cost F m _).trans (h.counts.altX _), clips _ _ _ hv.1 hv.2⟩
end Tips
end YM.UVExtension.Lacing.RoutesF

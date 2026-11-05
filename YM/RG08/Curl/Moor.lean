import YM.RG08.Curl.Quest
/-! # Once-lifts simultaneously to the boundary. Also a valid way to
 compare cutoffs without choosing a common arbitrary solution of Koszul. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums Staffer Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
open Chain Wings Summit
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {d q : ℕ}
structure Harbor (w : ℕ→ℝ) (ν:G.ColorIndex)(d:ℕ) where
  height : ℕ→ℝ
  charge : ℕ→ℝ
  pos i : 0<height i
  foil i : height i ≤ w i
  toll i : 0 ≤ charge i
  money i A (F:Panel G) : Fleet G ν F d → (∀ j≤d, Glow (F (j+2)) (w i) A) →
     ∃ T, Artefact F d (height i) (A*charge i) T
lemma harbors (h:G.Simple)(ν:G.ColorIndex)(w:ℕ→ℝ)(d:ℕ)(hp:∀i,0<w i): Nonempty (Harbor w ν d):= by choose v C hv hv' hc he using fun i=> boat h ν d (hp i); exact ⟨⟨_,_,hv,hv',hc,he⟩⟩

private lemma bundles {I:Type}{F:(i:I)→Panel G}{δ y w:I→ℝ} (h:∀ i≤d,Voucher y δ (fun j=>F j (i+2)) w)(he:0≤δ)(hp:Audience y): ∃ f, Weighed y f ∧ ∀ j i,i≤d→ Glow (F j (i+2)) (w j) (f j*δ j) := by
  let U (b:Fin (d+1)):= (h b.val (Nat.le_of_lt_succ b.isLt)).choose
  have hu i : Weighed y (U i):=(h _ (Nat.le_of_lt_succ i.isLt)).choose_spec.1
  have hs (s:Finset (Fin (d+1))): Weighed y (∑ i∈s,U i):= by
    induction s using Finset.induction_on with
    | empty=> rw [sum_empty]; exact Weighed.zero
    | insert i s hi ih=> rw [sum_insert hi]; exact (hu _).plus ih hp
  refine ⟨_,hs univ,fun j i hi=>?_⟩
  rw [Finset.sum_apply]; exact glow_less ((h i hi).choose_spec.2 j) le_rfl (mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i=> U i j) (fun i _=> (hu i).positive j) (mem_univ (⟨i,Nat.lt_succ_of_le hi⟩:Fin _))) (he j))

-- keep reps constant in cutoff S.given Wing domain at any fixed launched scale; restrict windows freely
variable (S) -- wrong S implicit
variable {S}
theorem ballast (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(H:Harbor S.η ν d)(hd:d+2*q ≤ E)(hY:Weighed (fun i:Launch u=> Launch.farY X i) (fun i=>H.charge (X.J i.i))):
    ∃ L:Launch u→ Flotilla G,∃ C:Launch u→ℝ, Weighed (Launch.farY X) C ∧
       (∀ l, Artefact (LimitWords X ν D q l.i) d (H.height (X.J l.i)) (C l) (L l)) ∧
       ∃ F : Wings u 0 → Flotilla G, ∃ A:Wings u 0→ℝ, Weighed (menu X) A ∧ ∀ t,
          Artefact (Words X ν D q t.i t.N) d (H.height (X.J t.i)) (C t.toLaunch + A t * chop X (1/4) t) (F t) ∧ Artefact (Words X ν D q t.i t.N - LimitWords X ν D q t.i) d (H.height (X.J t.i)) (A t * chop X (1/4) t) (F t-L t.toLaunch) := by
  have hh j (he:j≤d) := fleet_fund h hp hv hs (d:=j) (q:=q) (by omega)
  let V (i:Launch u):= LimitWords X ν D q i.i; let W (i:Wings u 0):= Words X ν D q i.i i.N
  let δ t:= chop X (1/4) (t:Wings u 0)
  have hc i : Fleet G ν (V i) d := Coals i h hp hv hs hd
  have ht t : Fleet G ν (W t) d:= baseCraft t hp hv
  obtain ⟨B,hB,Hb⟩:= bundles (F:=V) (y:= Launch.farY X) (w:=fun i=> Tier S i.i) (δ:=1) (d:=d) (fun i hi=> ((hh i hi).again).mold (fun i=> low (escalates i 0))) zero_le_one (Launch.you X)
  simp only [Pi.one_apply,mul_one] at Hb
  choose L hL using fun t:Launch u=> H.money _ _ _ (hc t) (Hb t)
  refine ⟨L,B*(fun i=> H.charge (X.J i.i)),hB.times hY,hL,?_⟩
  have hy t : Fleet G ν (W t - V t.toLaunch) d:= by
     apply Fleet.cross (ht t) (hc _ ) (S.positive _) (S.positive _) ((hh 0 (Nat.zero_le _)).fresh.choose_spec.2 t) (Hb _ 0 (Nat.zero_le _))
  obtain ⟨A,hA,H'⟩:= bundles (F:=fun i=> W i-V i.toLaunch) (fun i (hi:i≤ d)=> (hh i hi).moves) (fun _=> (gain_pos ..).le) (sh X)
  choose P hP using fun t:Wings u 0=> H.money _ _ _ (hy t) (H' t)
  refine ⟨fun t=> L t.toLaunch+P t, A * (fun t=> H.charge (X.J t.i)), hA.times (hY.transfer toLaunch),fun i=>?_⟩
  have he : ((A * (fun t:Wings u 0=> H.charge (X.J t.i))) i)*δ i=(A i*δ i)*H.charge (X.J i.i):= by rw [Pi.mul_apply]; ring
  have ht := Artefact.ride (hL i.toLaunch) (hP i) (H.pos _) (hc i.toLaunch).tune (hy i).tune
  constructor
  · rw [he]; rw [show Words X ν D q i.i i.N= V i.toLaunch+(W i-V i.toLaunch) from by abel]; exact ht
  rw [add_sub_cancel_left,he]; exact hP i
end YM.RG08.Virtue

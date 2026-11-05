import YM.RG08.Scale.Parley
/-! # All directions relative to reference, including with polynomial-length cost in age. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Conductor
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Push.AbsoluteSums UVExtension.Free PowerSeries Stationary
open scoped BigOperators Topology Real Classical
variable {I : Type} {y δ : I→ℝ} {r s : ℕ}
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g : KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {u : I→ Windows} {i k : ℕ}
open Wings

structure Roam (u : I→Windows) extends Wings u 0 where
   fromK : (u b).start ≤ (u b).k
   ends : (u b).k ≤ N
abbrev Roam.main (v:Roam u) := (u v.b).k
private abbrev zoom (i k : ℕ) := decide (k ≤ i)
def spanR (i k : ℕ) := if k ≤ i then i-k else k-i
-- note successive ratio v(j)/v(0). `k` is reference, `i` heading

def bright (i k j : ℕ) := if k ≤ i then k+j else k-(j+1)
lemma bright_span {i k j} (h:j<spanR i k) : min i k ≤ bright i k j ∧ bright i k j < max i k := by unfold bright spanR at *; split_ifs at * <;> omega

def kilometer (t : Roam u) := spanR t.i t.main
def road (s : DeckSeat (kilometer (u:=u)) 1) : Wings u 1 :=
    let t := s.i
    let V := t.toWings
    let i:= bright t.i t.main s.k
    have he := bright_span (i:=t.i) (k:=t.main) (j:=s.k) s.hw
    ⟨⟨V.b,i,(le_min V.geC t.fromK).trans he.1⟩,t.N,t.M,he.2.trans_le (max_le V.cut t.ends), V.side⟩
private lemma route_length (S : Schedule){i k} (h:i≤k) : (((k-i:ℕ):ℝ)*Real.log 2)≤ S.scale k-S.scale i := by
   induction k,h using Nat.le_induction with
   | base=> simp
   | succ k h ih=>
     have he:=downGill k S; rw [Nat.succ_sub h]; push_cast; linarith
abbrev Roam.measure (t:Roam u)(X:Chain):= menu X t.toWings
abbrev Roam.cost (t:Roam u)(X:Chain):= gain X.S (1/4) (max t.i t.main) t.N
lemma geo (X : Chain) : Weighed (fun i:Roam u=> i.measure X) (fun i=> (kilometer i:ℝ)) := by
  have he : 0 < Real.log 2:= Real.log_pos (by norm_num)
  refine ⟨(Real.log 2)⁻¹,1,(inv_pos.mpr he).le,fun i=>⟨Nat.cast_nonneg _,?_⟩⟩
  rw [pow_one,mul_comm,← div_eq_mul_inv]; apply (le_div_iff₀ he).mpr -- wrong
  let j:=i.main; change (((spanR i.i i.main):ℝ)*_ ≤ age X.S (u i.b).Z i.main i.i)
  unfold age spanR; have hh:0 ≤ (u i.b).Z:= (u i.b).pos
  split; next h=> rw [abs_of_nonneg (sub_nonneg.mpr (age_scale_mono _ h))]; linarith [route_length X.S h]
  next h=> have hp:=le_of_lt (lt_of_not_ge h); rw [abs_of_nonpos (sub_nonpos.mpr (age_scale_mono _ hp))]; linarith [route_length X.S hp]

lemma grow_budget (h:Circuit S ν D u)(hp : X.Wake G)(he : LocalRatio D)(hα:G.Simple) (hr:2*r ≤ E) : Lease (menu X) (chop X (1/4)) (fun i:Wings u 1=> Conductor.compass ν (lunar X ν D i) r) (fun i=> Conductor.compass ν (lunar X ν D i.wingR) r) := by
   by_cases hx:r=0
   · subst r; simp only [compass_zero]; exact Lease.const ..
   simp only [Conductor.compass,hx,↓reduceIte]; exact cost_probe ν (fun i=> S.positive _) (skater h hα hp he hr _).pre (h.cup.transfer toLaunch)
lemma leaseT {f g : I→ℝ}{v w:I→ℝ}(h:Lease y δ f g)(hv: Audience v)(hy: Weighed v y)(hx:δ≤w) : Lease v w f g :=
   ⟨hy.sway hv h.1,hy.sway hv h.2,_,hy.sway hv h.asset.choose_spec.1, fun i=> (h.asset.choose_spec.2 i).trans (mul_le_mul_of_nonneg_left (hx i) (h.asset.choose_spec.1.positive i))⟩
lemma choices {p:I→Prop} [DecidablePred p] (u:Audience y){f g h k:I→ℝ}(hf : Lease y δ f g)(hp:Lease y δ h k) (hd:0 ≤ δ) : Lease y δ (fun i=> if p i then f i else h i) (fun i=>if p i then g i else k i):= by
  refine ⟨(hf.has.plus hp.has u).mono (fun i=>norm_nonneg _) (fun i=>?_), (hf.also.plus hp.also u).mono (fun i=>norm_nonneg _) (fun i=>?_),?_⟩
  all_goals try (simp only [Pi.add_apply]; split; exact le_add_of_nonneg_right (norm_nonneg _); exact le_add_of_nonneg_left (norm_nonneg _))
  obtain ⟨A,hA,H⟩:= hf.asset; obtain ⟨B,hB,H'⟩:=hp.asset
  refine ⟨A+B,hA.plus hB u,fun i=>?_⟩
  split
  next h=> exact (H i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hB.positive _)) (hd _))
  next h=> exact (H' i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA.positive _)) (hd _))

def ratioLane (W : ℕ→Cues) (i k j : ℕ) := if k ≤ i then reform (W (bright i k j)) else muse (W (bright i k j))
def slag (X : Chain)(ν:G.ColorIndex)(D:ChartRatio G)(N i) := Conductor.compass ν (X.compassRaw ν D N i)
theorem ratios_ge {W:ℕ→Cues} (h:∀ j,W j 0=1) (i k j) : ratioLane W i k j 0=1:= by unfold ratioLane; split; rw [reform_zero,h]; exact muse_unit (h _)
-- applied to both histories
private def SeatsL (u : I→Windows):= DeckSeat (kilometer (u:=u)) 1
lemma tier_age (X : Chain) (i : DeckSeat (kilometer (u:=u)) 1) : menu X (road i) ≤ i.i.measure X := by
  change age X.S (u i.i.b).Z i.i.main (bright i.i.i i.i.main i.k) ≤ age X.S _ i.i.main i.i.i
  have he:= bright_span (i:=i.i.i) (k:=i.i.main) (j:=i.k) i.hw
  unfold age
  by_cases h:i.i.i < i.i.main
  · rw [max_eq_right h.le,min_eq_left h.le] at he
    rw [abs_of_nonpos (sub_nonpos.mpr (age_scale_mono _ he.2.le)),abs_of_nonpos (sub_nonpos.mpr (age_scale_mono _ h.le))]; linarith [age_scale_mono X.S he.1]
  push Not at h
  rw [min_eq_right h,max_eq_left h] at he
  rw [abs_of_nonneg (sub_nonneg.mpr (age_scale_mono _ he.1)),abs_of_nonneg (sub_nonneg.mpr (age_scale_mono _ h))]; linarith [age_scale_mono X.S he.2.le]
lemma books (h : Circuit S ν D u)(hp:X.Wake G)(he:LocalRatio D)(hα:G.Simple)(v r:ℕ) (hr:2*r ≤ E) : Lease (fun i:DeckSeat (kilometer (u:=u)) 1=> Roam.measure i.i X) (fun i=>Roam.cost i.i X) (fun i=> ratioLane (slag X ν D i.i.N) i.i.i i.i.main i.k r) (fun i=>ratioLane (slag X ν D i.i.M) i.i.i i.i.main i.k r) := by
  let y t:= Roam.measure (DeckSeat.i (L:=kilometer (u:=u)) (t:=1) t) X
  let δ t:= Roam.cost (DeckSeat.i (L:=kilometer (u:=u)) (t:=1) t) X
  let Mu t:= chop X (1/4) (road (u:=u) t)
  let Uu t:= menu X (road (u:=u) t)
  have ha : Audience y:= fun i=> sh X _
  have hx : Weighed y Uu:= (show Weighed y y by simpa only [pow_one] using Weighed.power y ha 1).mono (fun i=>zero_le_one.trans (sh X _)) (tier_age X)
  have hV : Mu ≤ δ := by
    intro i
    apply Real.exp_monotone; have hz: (road i).i ≤ max i.i.i i.i.main:= (bright_span (i:=i.i.i) (k:=i.i.main) (j:=i.k) i.hw).2.le
    change -(1/4:ℝ)*(X.S.scale i.i.N-X.S.scale (road i).i) ≤ _; linarith [age_scale_mono X.S hz]
  have hc i hi:= leaseT (Summit.Lease.whirls (grow_budget h hp he hα (show 2*i≤ E from Nat.le_trans (Nat.mul_le_mul_left _ (hi:i≤r)) hr)) road) ha hx hV
  let V t:= slag X ν D (road (u:=u) t).N (road t).i; let Q t:= slag X ν D (road (u:=u) t).M (road t).i
  have hP:= Lease.reforming (f:=V) (g:=Q) ha hc r le_rfl; have hQ:= Lease.undo (f:=V) (g:=Q) ha hc (fun _=>compass_zero ..) (fun _=> compass_zero ..) r le_rfl
  change Lease y δ _ _; unfold ratioLane
  -- if pushed through r
  simp only [apply_ite (fun x:Cues=> x r)] -- maybe
  exact choices ha hP hQ (fun _=>(gain_pos ..).le)

def rootsRatio (X : Chain) (ν:G.ColorIndex)(D:ChartRatio G)(N i k) := paths (ratioLane (slag X ν D N) i k) (spanR i k)
lemma tolls_paid (h:Circuit S ν D u)(hp:X.Wake G)(he:LocalRatio D)(hα:G.Simple)(hr:2*r ≤ E) : Lease (fun i:Roam u=> i.measure X) (fun i=> i.cost X) (fun i=> rootsRatio X ν D i.N i.i i.main r) (fun i=> rootsRatio X ν D i.M i.i i.main r) := by
    let F (t:Roam u):= ratioLane (slag X ν D t.N) t.i t.main
    let H (t:Roam u):= ratioLane (slag X ν D t.M) t.i t.main
    exact Summit.Lease.whirls (route_paid (y:=fun i:Roam u=> i.measure X) (δ:=fun i:Roam u=>i.cost X) (E:=r) (L:=kilometer) (F:=F) (H:=H) (r:=r) (fun _ _ _=>ratios_ge (fun _=> compass_zero ..) ..) (fun _ _ _=>ratios_ge (fun _=> compass_zero ..) ..) (fun i=> sh X _) (fun i=> (gain_pos ..).le) (geo X) (fun k hk=> books h hp he hα E k (show 2*k≤ E from Nat.le_trans (Nat.mul_le_mul_left _ (hk:k≤r)) hr)) le_rfl) (fun i=>⟨i,kilometer i,le_rfl⟩)

lemma rooted_unit (N i k) : rootsRatio X ν D N i k 0=1:=route_one _ _ fun _ _=>ratios_ge (fun _=> compass_zero ..) ..
-- all adjacent equations as formal series about reference; ensures compositions for any admitted direction coincide. Include `b` orientation
private lemma sooner {F G : ℕ→Cues}{k : ℕ}(h : ∀ i<k,F i=G i): paths F k=paths G k:= by induction k with | zero=> rfl| succ k ih=> rw [paths,paths,ih (fun i hi=> h i (by omega)),h k (by omega)]
lemma march_next (W:ℕ→Cues)(h:∀ j,W j 0=1)(i k:ℕ):
    let A:= paths (ratioLane W i k) (spanR i k)
    let B:= paths (ratioLane W (i+1) k) (spanR (i+1) k)
    Span B=Span A * PowerSeries.subst (Span B) (PowerSeries.mk (W i)):= by
    intro A B
    by_cases ht : k ≤ i
    · have he : spanR (i+1) k=spanR i k+1:= by unfold spanR; split_ifs <;>omega
      rw [show B=glide A (reform (W i)) from ?_]; · exact glide_toward A (W i)
      unfold B; rw [he,paths]; unfold A
      have hw : ∀ j, ratioLane W i k j=ratioLane W (i+1) k j:= fun i=> by simp [ratioLane,bright,ht,ht.trans (Nat.le_succ _)]
      rw [funext (fun j=> (hw j).symm)]; unfold ratioLane; rw [if_pos ht]; rw [show bright i k (spanR i k)= i by unfold spanR bright; split_ifs <;>omega]
    have hp : spanR i k=spanR (i+1) k+1:= by unfold spanR; split_ifs <;>omega
    have he : A=glide B (muse (W i)):= by
      unfold A; rw [hp,paths]
      have hZ : paths (ratioLane W i k) (spanR (i+1) k)=B:= by
        apply sooner; intro j hj
        unfold spanR at hj; split at hj; next h=> omega
        unfold ratioLane bright; split_ifs <;> first|omega|rfl
      rw [hZ]; unfold ratioLane; rw [if_neg ht]; rw [show bright i k (spanR (i+1) k)= i by unfold spanR bright; split_ifs <;>omega]
    rw [he]; exact glide_before B (W i) (h _)
lemma across_all (N i k) : let V := rootsRatio X ν D N (i+1) k; let U:= rootsRatio X ν D N i k
    Span V=Span U * PowerSeries.subst (Span V) (PowerSeries.mk (slag X ν D N i)) := march_next (slag X ν D N) (fun _=> compass_zero ..) _ _
lemma full_at (N i:ℕ) : PowerSeries.mk (rootsRatio X ν D N i i)=1:= by
    ext n; rw [coeff_mk]; unfold rootsRatio spanR; rw [if_pos le_rfl,Nat.sub_self]; rfl
end YM.RG08.Conductor

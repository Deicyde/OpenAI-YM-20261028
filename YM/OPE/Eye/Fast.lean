import YM.OPE.Shape
import YM.OPE.Eye.Remit
/-!
# Two-scale phase moment price

Price holds with engineering powers on both ext and clusters. These are
prices of entire words. Uniformly suffices for interpolation arbitrarily
high order if chosen after fixing arity, budget & differentiations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Wilson Cells Extraction Word Cards Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U : Final C F S) (h : Org.Grill C F)
variable {I J L : Type}[Fintype I][Fintype J] {φ:Filter L} {T:L→ℝ}{a b c d e q g δ : ℝ}
variable {k k' f n v v' m j : L→ℕ}
variable (x:I→ C.book.Token)(y:J→ C.book.Token) {X:L→I→ E4}{Y:L→J→ E4}(hT:Tendsto T φ atTop)[φ.NeBot]

def sigma {G:Gauge}{S:Register G}(x:I→ S.Token) : ℕ := ∑ i,(x i).1
include hT U
lemma admitted (h:Height C.S φ T k a)(hd:0<δ) : ∃ μ : L → I→ℝ, RateIs φ T (fun i=>∏ j,μ i j) (((↑(sigma x):ℝ)+δ*Fintype.card I)*a) ∧ ∀ᶠ i in φ, Prepared (C:=C) x F (k i) (μ i):=by
    let R(i:I):ℝ:= 1+‖(x i).2‖; have hR(i:I):0<R i:= add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)
    choose t ht Y hY hu using fun i=> U.room.copies.centered (x i).1 δ (R i) hd (hR i)
    let f(i:L)(j:I):=(C.S.a (k i)) ^ (-(↑(x j).1:ℝ) - δ); let w (i:L)(j:I):=(1+Y j)*f i j + 1; have hp j:a*0≤ (((x j).1+δ)*a) :=by rw [mul_zero]; exact mul_nonneg (by positivity) (h.nonneg hT)
    have hz(j:I):RateIs φ T (fun i=> w i j) (((x j).1 + δ)*a):=((RateIs.const hT (add_pos_of_pos_of_nonneg one_pos (hY j))).mul (h.mesh.rpow (-(↑(x j).1:ℝ)-δ))|>.add (RateIs.const hT one_pos) hT).swap (by
       rw [zero_add,show (-(↑(x j).1:ℝ)-δ)*(-a)=(((x j).1:ℝ)+δ)*a from by ring]; exact max_eq_left (by linarith only [hp j]))
    refine ⟨w,(RateIs.prod (S:= Finset.univ) (fun j _=> hz j) hT).swap ?_ ,?_⟩
    · rw [← Finset.sum_mul,Finset.sum_add_distrib]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sigma,Nat.cast_sum]; ring
    filter_upwards [eventually_all.mpr fun j:I=> h.grows.eventually_ge_atTop (t j)] with i hi; constructor; intro j
    rw [Extraction.Order.fused]; refine (hu j _ (hi j) 1 one_pos).mono fun s hs=> hs.mono fun n ⟨hn,hN⟩=>?_ ; obtain ⟨hw,hV⟩:=hN (x j).2 (le_add_of_nonneg_left zero_le_one) 0; exact ⟨hn,hw,hV.trans (add_le_add_left (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (show 0 ≤ f i j from (Real.rpow_pos_of_pos (C.S.a_pos (k i)) _).le)) 1)⟩

omit U [φ.NeBot] in
lemma hall_range
    (hf:Height C.S φ T f a)(hv:Height C.S φ T v b)(hu:Height C.S φ T m c)(hp:Height C.S φ T n d)(hq:Height C.S φ T k e)
    (he:a<c)(hh:c<b)(hl:c<e)(hz:b<d)(I J :ℕ) : ∀ᶠ i in φ, Hall C.S (f i) (v i) (k i) (m i) (n i) I J:=by
    have hA:= RateLE.const (2:ℝ) hT; have hy:=hf.mesh.overtakes ((RateLE.const (I:ℝ) hT).mul (hA.mul ((RateLE.const (5:ℝ) hT).mul (hu.mesh.pays hT)))) hT (by linarith)
    have hw:= hv.mesh.overtakes ((RateLE.const (J:ℝ) hT).mul (hA.mul ((RateLE.const (3:ℝ) hT).mul (hp.mesh.pays hT)))) hT (by linarith)
    filter_upwards [hf.earlier he hT hu,hu.earlier hh hT hv,hu.earlier hl hT hq,hv.earlier hz hT hp,hy,hw] with i h h' hG hM hi hy using ⟨h.le,h'.le,hG.le,hM.le,hi,hy⟩
omit U [φ.NeBot] in
lemma Moment_gap (hf:Height C.S φ T f a)(h:a>b): RateLE φ T (fun i=>2*C.S.a (f i)) (-a):=by simpa only [zero_add] using (RateLE.const (2:ℝ) hT).mul (hf.mesh.pays hT)

include h
private lemma slack (hX:Kept φ T a X)(hY:Kept φ T b Y)(hp:Intervals φ T a X Y)
    (hK:Height C.S φ T f c) (hV:Height C.S φ T m d)(hB:Height C.S φ T k e)(hH:Height C.S φ T v g)(hI:Height C.S φ T n q)(ha:a<c)(he:c<d)(hg:d<e)(hU:d<g)(hb:b<g)(hu:g<q)(hd:0<δ) : RateLE φ T (fun i=> viewing U (beside (X i) (Y i)) (beside x y)) (((↑(sigma x):ℝ)+δ*Fintype.card I)*e+(((sigma y:ℕ):ℝ)+δ*Fintype.card J)*q):= by
    obtain ⟨μ,χ,hw⟩:= admitted U x hT hB hd; obtain ⟨μ',χ',hw'⟩:= admitted U y hT hI hd
    apply ((χ.mul χ').pays hT).of_norm_le; filter_upwards [hw,hw',hX.short ha hT (Moment_gap hT hK ha), hY.short hb hT (Moment_gap hT hH hb), hp.short ha hT (Moment_gap hT hK ha), hall_range hT hK hH hV hI hB he hU hg hu (Fintype.card I) (Fintype.card J)] with i hi h hr hz hp hE using civic U ‹Org.Grill C F› hr hz hp hE hi h
-- both main A and ext B, arbitrary frames. Cross minimum exponent tested.
lemma phase_budget (hX:Kept φ T a X)(hY:Kept φ T b Y)(hp:Intervals φ T a X Y)(ha:0≤a)(hu:a≤b) : RateLE φ T (fun i=> viewing U (beside (X i) (Y i)) (beside x y)) ((↑(sigma x):ℝ)*a+(↑(sigma y):ℝ)*b):=by
    intro u hξ; obtain ⟨δ,hδ,hF⟩: ∃ δ:ℝ, 0 < δ ∧ (↑(sigma x)+δ*Fintype.card I)*(a+δ) + (↑(sigma y)+δ*Fintype.card J)*(b+δ) < u:=by
       have he : ∀ᶠ δ:ℝ in 𝓝[>] 0, (↑(sigma x)+δ*Fintype.card I)*(a+δ) + (↑(sigma y)+δ*Fintype.card J)*(b+δ)<u:= by refine ((show Continuous fun δ:ℝ=> (↑(sigma x)+δ*Fintype.card I)*(a+δ)+(↑(sigma y)+δ*Fintype.card J)*(b+δ) from by fun_prop).continuousAt.tendsto.eventually (p:=fun x=>x < u) ?_).filter_mono nhdsWithin_le_nhds; exact gt_mem_nhds (by simpa using hξ)
       exact ((show ∀ᶠ v:ℝ in 𝓝[>] 0,0<v from self_mem_nhdsWithin).and he).exists
    have hP:= C.path.levels.fits.mesh; obtain ⟨f,h₁⟩:= found hT hP (show 0≤a+δ/3 by positivity); obtain ⟨m,h₂⟩:= found hT hP (show 0≤a+δ/2 by positivity); obtain ⟨k,h₃⟩:= found hT hP (show 0≤a+δ by linarith only [ha,hδ]); obtain ⟨v,h₄⟩:= found hT hP (show 0≤ b+3*δ/4 by linarith only [ha,hu,hδ]); obtain ⟨n,h₅⟩:= found hT hP (show 0≤ b+δ by linarith only [ha,hu,hδ]);
    exact slack U h x y hT hX hY hp h₁ h₂ h₃ h₄ h₅ (by linarith only [hδ]) (by linarith) (by linarith) (by linarith only [hu,hδ]) (by linarith only [hδ]) (by linarith only [hδ]) hδ _ hF
lemma viewer_cost (s:L→Viewers U)(hX:Kept φ T a X)(hY:Kept φ T b Y)(hp:Intervals φ T a X Y)(ha:0≤a)(hu:a≤b): RateLE φ T (fun i=> observe (spectator U (s i)) (beside (X i) (Y i)) (beside x y)) ((↑(sigma x):ℝ)*a+(↑(sigma y):ℝ)*b):=by
    apply (phase_budget U h x y hT hX hY hp ha hu).transfer
    filter_upwards [(hX.mono hu|>.chorus hY (hp.mono hu)|>.inject)] with i hi; rw [← glance_sees U _ _ _ hi]; exact glance_bound ..
lemma viewer_alt (s:L→Viewers U)(hX:Kept φ T a X)(hY:Kept φ T b Y)(hp:Intervals φ T b X Y)(ha:0≤b)(hu:b≤a): RateLE φ T (fun i=> observe (spectator U (s i)) (beside (X i) (Y i)) (beside x y)) ((↑(sigma x):ℝ)*a+(↑(sigma y):ℝ)*b):=by
    rw [add_comm]; apply (viewer_cost U h y x hT s hY hX hp.swap ha hu).congr
    filter_upwards [(hX.chorus (hY.mono hu) (hp.mono hu)).inject] with i hi; have he := (spectate U (s i)).laws.toSymmetric; have hp := perm_observe (spectator U (s i)) he (Equiv.sumComm J I) (beside x y) hi
    rw [show (beside (X i) (Y i)) ∘ Equiv.sumComm J I=beside (Y i) (X i) from funext fun x=> by cases x <;> rfl,show beside x y ∘ Equiv.sumComm J I=beside y x from funext fun x=> by cases x <;> rfl] at hp; exact hp
end YM.OPE

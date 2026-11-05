import YM.OPE.Trees.Regime
/-!
# Background probes have clearance from this family of trees

Pushed into substeps on the tree individually as needed. `graces` pays
also for eventual lifetimes of finitely supported detectors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset
open scoped Classical Topology ContDiff BigOperators
variable {I J L K : Type}[Fintype I][Fintype J][Fintype K]{φ : Filter L}{s:Arboreal I}{a b: Finset I}{t r:I→ℝ}{X:I→E4}
    {p M δ c σ0:ℝ}{i j k:I}{x:L→I→E4}{R:L→I→ℝ}{y:L→J→ E4}{X' : K→ E4}{z z':L→ E4}
    (h:s.Coterie φ t M δ x R)
local notation "T!"=> (fun i:L=>s.fullLife (R i))
/-- Root backgrounds may vary (on any translations and also unbounded
clearance-preserving shape changes); cap of arity & labels fixed by its use.
-/
def Backdrop (φ:Filter L)(x:L→ E4) (y:L→ J→ E4) := ∃ c:ℝ, 0<c ∧ ∀ᶠ i in φ, ClearOf (x i) (y i) c
lemma Backdrop.at (he:Backdrop φ z y)(hx:Tendsto (fun i=> ‖z' i-z i‖) φ (𝓝 0)):Backdrop φ z' y:=by
    obtain ⟨c,hc,hf⟩:=he; refine ⟨c/2,by positivity,?_⟩; filter_upwards [hf,hx.eventually_le_const (show 0<c/2 from (by positivity))] with i hi hk; refine ⟨fun j=> ?_,fun j k hj=> (half_le_self hc.le).trans (hi.spread j k hj)⟩; linarith only [hk,hi.openSpace j, c_dist_point (z i) (z' i) (y i j), norm_sub_rev (z' i) (z i)] -- lemma name

def register {G:Gauge}{L:Register G}(x:Exterior L)(o:E4) : Fin x.n→ E4:=fun i=> bearing x i + o
lemma shelf {G:Gauge}{R:Register G}(x:Exterior R)(o:L→E4): Backdrop φ o (fun i=>register x (o i)):=by
    obtain ⟨hm,hx,he⟩:= beside_distinct.mp (bearing_clear x);
    have hp (i:Fin x.n): 0 < ‖bearing x i‖:= norm_pos_iff.mpr (show bearing x i≠0 from Ne.symm (he () i));
    have hv (i j: Fin x.n)(h:i≠j): 0 < ‖bearing x i-bearing x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne h));
    have hw (c:ℝ)(h:0<c): ∀ᶠ i:ℝ in 𝓝[>]0,i ≤ c:= (ge_mem_nhds h).filter_mono nhdsWithin_le_nhds
    obtain ⟨c,hc,hv1,hv2⟩:= ((show ∀ᶠ i:ℝ in 𝓝[>]0,0 < i from self_mem_nhdsWithin).and ((eventually_all.mpr (fun i:Fin x.n=> hw _ (hp i))).and (eventually_all.mpr (fun i:Fin x.n=>eventually_all.mpr (fun j:Fin x.n=> eventually_all.mpr (fun hh=> hw _ (hv i j hh))))))).exists -- filter_mono needed
    exact ⟨c,hc,Eventually.of_forall (fun i=> ⟨fun j=> (by simpa [norm_sub_rev (o i),register] using hv1 j),fun j k hh=> by simpa [register] using hv2 j k hh⟩)⟩

variable {G:Gauge}{A:Register G}(w:Exterior A)
variable {x':I→ E4} {o':E4}
lemma away_bearing : beside (away x' o') (bearing w)= away (beside x' (register w o')) o':= funext fun j=> by rcases j with j|j <;> simp [away, register]
lemma record_raw (S:Table A)(h0:S.Hierarchy)(v:I→ A.Token)(he:Injective (beside x' (register w o'))) :
    Prescription.reading S x' v o' w = observe S (beside x' (register w o')) (beside v w.letter):= by
    unfold Prescription.reading; have hp:= (away_inject _ o').2 he; rw [← away_bearing w] at hp; change (if Injective (beside (away x' o') (bearing w)) then observe S (beside (away x' o') (bearing w)) _ else 0)= _; rw [if_pos hp,away_bearing]; exact observe_away S _ _ o' h0.translations he

variable (he:Backdrop φ (fun j=> x j s.root) y)(hv:s.Active a)
include h he
lemma Backdrop.rooted (i:I) : Backdrop φ (fun j=> x j i) y:= he.at (h.closes s.initial (s.closure i))
lemma Backdrop.life (i:I): Kept φ T! 0 y ∧ Intervals φ T! 0 (fun j=>sole (x j i)) y:=by obtain ⟨c,hc,hp⟩:= he.rooted h i; exact free_clear h.time hc hp
lemma Backdrop.around (b:Finset I): Intervals φ T! 0 (fun j=>crop (x j) b) y:=by
    intro p hp; refine eventually_all.mpr fun i:(↑b:Type)=>?_ ; filter_upwards [(he.life h i.val).2 p hp] with i' h' k using (h' () k)
include hv in
lemma overall_injected : ∀ᶠ k in φ, Injective (beside (crop (x k) (s.live a)) (y k)):=(((h.eternity hv (Finset.Subset.refl ..)).chorus ((he.life h s.root).1.mono zero_le_one) ((he.around h (s.live a)).mono zero_le_one))|>.inject)
lemma Backdrop.registered (k:I)(ht:Kept φ T! p (fun j=>crop (x j) b)): ∀ᶠ j in φ, Injective (beside (crop (x j) b) (y j)):=
    ((ht.mono (le_max_left ..)).chorus ((he.life h k).1.mono (le_max_right ..)) ((he.around h b).mono (le_max_right ..)))|>.inject
-- pitches for shelf uses he center k not necessarily root S. k arbitrary descendant? here Shift detector x k. Backdrop for root follows as Tendsto zroot-zk. handle Pin.
omit he
lemma Backdrop.child (k:I): Backdrop φ (fun j=> x j s.root) (fun j=>register w (x j k)):= (shelf _ _).at (by simpa only [norm_sub_rev _ (x _ k)] using h.closes s.initial (s.closure k)) -- simp rewrite loop
lemma Coterie.pinned (k:I)(b:Finset I)(hk:Kept φ T! p (fun j=>crop (x j) b)) : ∀ᶠ j in φ, Injective (beside (away (crop (x j) b) (x j k)) (bearing w)):=by
    filter_upwards [(Backdrop.child h w k|>.registered h k hk)] with j hi; rw [away_bearing w,away_inject]; exact hi
end YM.OPE.Arboreal

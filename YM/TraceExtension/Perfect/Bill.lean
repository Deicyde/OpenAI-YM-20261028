import YM.TraceExtension.Perfect.Crawl
import YM.Next.FREE_KERNELS.Differences
import YM.Corona.Spend

/-!
# Front centered free bounds; no periodic losses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Matrix Lattice Precision Laurent Stationary Bloch Next.Free Exterior Finset
open scoped BigOperators Topology ContDiff
variable {c f : Side}{g : Ratio c f} {α β:Type}[Fintype α][DecidableEq α][Fintype β]{W:Cross g.count α β}{η σ C:ℝ}{t:ℕ}
-- real polynomial cost absorption. can choose after stage only.
omit [Fintype α] in
lemma shelter_paid {t:ℕ}{η α:ℝ}(h:0≤α)(hp:α<η): ∃ D:ℝ,0<D ∧ ∀ r:ℝ,0 ≤ r→ shelter α t r ≤ D*Real.exp (η*r) :=by
 let b:ℝ:= (η-α)/(t+1); have hb:0 < b:=div_pos (sub_pos.mpr hp) (by positivity)
 let K:=1+b⁻¹; have hK:0<K:=add_pos zero_lt_one (inv_pos.mpr hb)
 refine ⟨K^t,pow_pos hK _,fun r hr=> ?_⟩
 have hx : 1+r≤ K * Real.exp (b*r):=by
     apply le_trans _ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hK.le)
     unfold K; rw [add_mul,mul_add b⁻¹,inv_mul_cancel_left₀ hb.ne']; linarith [mul_nonneg hb.le hr,inv_pos.mpr hb]
 unfold shelter; refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx t) (Real.exp_pos _).le).trans ?_
 rw [mul_pow,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK.le t)
 apply Real.exp_monotone; rw [← mul_assoc,← add_mul]; apply mul_le_mul_of_nonneg_right _ hr
 have h0:0 < (t:ℝ)+1:=by positivity
 rw [← le_sub_iff_add_le]; unfold b; rw [← mul_div_assoc, div_le_iff₀ h0]; nlinarith only[hp]

private lemma spacing {y z:Site f}(v:Site c) (T R :ℝ)(r:ℝ) (w: Site c) (hh:(separation y z:ℝ)≤(g.count.val:ℝ)*(T+r)) (he:(separation (g.embed v) y:ℝ) ≤ (g.count.val:ℝ)*R) (ht:0 ≤ T)(hR:0≤R):
  max 0 ((separation v w:ℝ)-r) ≤ T+R+separation z (g.embed w)/(g.count.val:ℝ):=by
 have h:= Corona.below g v w
 let L:ℝ:= g.count.val; have hp:0<L:= side_pos _
 have hv : L*separation v w ≤ (L*R+L*(T+r))+(separation z (g.embed w):ℝ) :=by
      calc
       _ ≤ (separation (g.embed v) (g.embed w):ℝ) := by unfold L; exact_mod_cast h
       _ ≤ ((separation (g.embed v) y:ℝ)+(separation y z:ℝ))+(separation z (g.embed w):ℝ) := by exact_mod_cast (separation_triangle (g.embed v) z (g.embed w)).trans (Nat.add_le_add_right (separation_triangle _ y z) _)
       _ ≤ _:=add_le_add (add_le_add he hh) le_rfl
 apply max_le (show 0≤ T+R+(separation z (g.embed w):ℝ)/L from by positivity); change _ ≤ _+ (separation z (g.embed w):ℝ)/L
 apply le_of_mul_le_mul_left _ hp; rw [mul_add,_root_.mul_div_cancel₀ _ hp.ne']
 linarith only [hv]

-- support shape in fine units. rounded ratios never cost factors
omit [Fintype α] [DecidableEq α] in
lemma odometer (g : Ratio c f)(v:Site c)(o:Site f)(R T r:ℝ)(z:Site f)(he:(separation o z:ℝ)≤(g.count.val:ℝ)*(T+r))(hg:(separation (g.embed v) o:ℝ) ≤ (g.count.val:ℝ)*R)(ht:0 ≤ T)(hR:0≤R) {W:Cross g.count α β}(h:W.strip η C) (ha:0≤σ)(hb: σ<η) {D:ℝ}(hp:0<D)(hd:∀ r:ℝ,0≤r→shelter σ t r ≤ D*Real.exp (η*r)) (i:α):
    sh (fun j:Co c β=> separation v j.1) σ t r (installed g W (z,i)) ≤ (D*Real.exp (η*(T+R)))* (Real.exp η*(Fintype.card β*C)) :=by
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (cross_sprawl g (ha.trans hb.le) h (z,i)) (show 0 ≤ D*Real.exp _ from mul_nonneg hp.le (Real.exp_pos _).le)); unfold sh; rw [Finset.mul_sum]; apply sum_le_sum; intro a _
 rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 dsimp only [spot]
 apply le_trans ((hd _ (le_max_left ..)).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (spacing v T R r a.1 he hg ht hR) (ha.trans hb.le))) hp.le))
 unfold crossW; rw [mul_add, Real.exp_add, mul_assoc]

--
private lemma stap_move {i:Axis} (W:Cross g.count α β)(x:Site f)(a:α)(h:Odd g.count.val) (hw:Whole W) :
   installed g W (x+step i,a)-installed g W (x,a) = installed g (forwardC g.count W i) (x,a) := by
   rw [← move_forward h, Whole.from_fine g (knock_whole α i) hw]
   funext b; exact (knock_entry α _ i (x,a) (fun t=> installed g W t b) |>.symm)

def cab (g:Ratio c f) (W:Cross g.count α β) (x:Site f)(a:α)(v:Cover):= installed g W (wrap f v+x,a)
lemma cab_move (g:Ratio c f) (W:Cross g.count α β) (v:Axis)(a:α)(x:Site f) (h:Odd g.count.val) (hw:Whole W) :
    move (cab g W x a) v=cab g (forwardC _ W v) x a :=by
    funext i; unfold cab move; dsimp only; rw [map_add,wrap_step, add_right_comm,stap_move _ _ _ h hw]

end YM.Trace.Perfect

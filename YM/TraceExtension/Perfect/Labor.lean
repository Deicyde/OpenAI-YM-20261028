import YM.TraceExtension.Perfect.GaugeFoot

/-!
# Room for all curvature coordinates at marginal gain
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Matrix Lattice Precision Laurent Stationary Bloch Next.Free Exterior Finset
open scoped BigOperators Topology ContDiff
variable {f c:Side}
abbrev roof (x:Site c) {α:Type}(i:Co c α):= separation x i.1
private lemma close_walk (v : Cover)(o : Site f): separation o (wrap f v+o)≤size v:=by rw [separation_comm,separation, add_sub_cancel_right]; exact within_size ..

lemma ambient_size (x : Site f): size (lift x)≤ 4*pdist x:= by unfold Laurent.size; calc
 _ ≤ ∑ _i:Axis,pdist x:= sum_le_sum fun i _=> component_le x i
 _=_:=by simp [Axis]
lemma component_cost (o x: Site f)(i): |(lift (x-o) i:ℝ)|≤separation x o:=by exact_mod_cast (by have := component_le (x-o) i; rw [abs_le]; omega : |lift (x-o) i| ≤ (pdist (x-o):ℤ))

def bloom (g:Ratio c f)(W:Cross g.count (TypeFace 1) (TypeFace 1))(x:Site f)(i:Body 1 f): Body 1 c→ℝ:= lin (cab g W x i.2) (lift (i.1-x))
def hingeQ (g:Ratio c f)(W:Cross g.count (TypeFace 1) (TypeFace 1))(x:Site f)(i:Body 1 f): Body 1 c→ℝ:= quad (cab g W x i.2) (lift (i.1-x))

theorem peg (α η E T:ℝ)(t:ℕ)(ha:0 ≤ α)(hp:α<η)(he:0 ≤ E)(hT:0≤T):
    ∃ C :ℝ,0 ≤ C ∧ ∀ (c f:Side)(g:Ratio c f)(W:Cross g.count (TypeFace 1) (TypeFace 1)), Odd g.count.val→
     (∀ l:List Axis,l.length ≤ 3→ (advanceC _ W l).strip η (E/(g.count.val:ℝ)^(1+l.length)))→
     8*(g.count.val+1)+4 ≤ f.val → ∀ (v:Site c)(x:Site f), (separation (g.embed v) x:ℝ) ≤ T*g.count.val →
        Settle (roof v) (fun j:Body 1 f => separation j.1 x) (fleece (installed g W) (g.count.val+1) x) (bloom g W x) (hingeQ g W x) α t g.count.val C :=by
 obtain ⟨D,hD,hd⟩:= shelter_paid (t:=t) ha hp
 let F:= (D* Real.exp (η*(4+T)))* (Real.exp η*(Fintype.card (TypeFace 1)*E)); let C:=100*F; have hF:0 ≤ F:=by unfold F; positivity
 refine ⟨C,by unfold C; positivity,fun c f g W ho hw hn v x hx=>?_⟩
 rw [mul_comm T] at hx
 let L:ℝ:= g.count.val; let b:= g.count.val+1; let Q:=cab g W x; let A:= installed g W; let R (q:Body 1 c):=roof v q; have hη := lt_of_le_of_lt ha hp; have hL : 0<L:= side_pos _
 have hf(l:List Axis)(ht:l.length ≤ 3):=(hw l ht)
 have hm(l:List Axis)(ht:l.length ≤ 3): Whole (advanceC _ W l):= ⟨_,_,hη,hf l ht⟩
 have hP(l:List Axis)(h:l.length≤ 3)(z:Site f)(r:ℝ)(hi:(separation x z:ℝ)≤L*(4+r))(i:TypeFace 1): sh R α t r (installed g (advanceC _ W l) (z,i))≤F/L^(1+l.length):=by
    refine (odometer g v x T 4 r z hi hx (by norm_num) hT (hf l h) ha hp hD hd _).trans_eq ?_; unfold F L; ring
 have hX(z:Site f)(r:ℝ)(h:(separation x z:ℝ) ≤ L*(4+r))(i:TypeFace 1): sh R α t r (A (z,i)) ≤ F/L:=by
    simpa only [A,advanceC,List.length_nil,add_zero,pow_one] using hP [] (by simp) z r h i
 have hu (i a w s): move (move (move (Q s) i) a) w=cab g (advanceC _ W [w,a,i]) x s:=by
    unfold Q; erw [cab_move _ _ _ _ _ ho (hm [] (by simp)), cab_move _ _ _ _ _ ho (hm [i] (by simp)), cab_move _ _ _ _ _ ho (hm [a,i] (by simp))]; rfl
 have h' (i a s): move (move (Q s) i) a=cab g (advanceC _ W [a,i]) x s:=by
    unfold Q; erw [cab_move _ _ _ _ _ ho (hm [] (by simp)),cab_move _ _ _ _ _ ho (hm [i] (by simp))]; rfl
 have he' (s : TypeFace 1)(z: Cover)(i:Axis)(hz:(size z:ℝ) ≤ 4*L): sh R α t 0 (move (Q s) i z) ≤ F/L^2:=by
    unfold Q; erw [cab_move _ _ _ _ _ ho (hm [] (by simp))]; apply hP [i] (by simp) (wrap f z+x) 0 ?_ s
    rw [add_zero,mul_comm]; exact (Nat.cast_le.mpr (close_walk z x)).trans hz
 have hf0(u:Site f)(i)(h:(separation u x:ℝ)≤L): fleece A b x (u,i)=Q i (lift (u-x))-Q i 0:=by
    obtain ⟨j,hj⟩:= axisEquiv.surjective i; subst i; change fleece A b x (u,coord j)=_; rw [fleece_card _ _ _ _ _ (show separation u x < b from Nat.lt_succ_of_le (Nat.cast_le (α:=ℝ)|>.mp h)), beam_alive x u b hn (show separation u x < b from Nat.lt_succ_of_le (Nat.cast_le (α:=ℝ)|>.mp h))]
    simp [Q,b,cab,A]
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i hi=>?_⟩
 · rcases i with ⟨k,u⟩
   let r:=separation k x; let z := lift (k-x)
   change sh R α t ((r:ℝ)/L) (fleece A b x (k,u)) ≤ C*_ ; by_cases h : (r:ℝ) ≤ L
   · rw [hf0 _ _ h]; apply (sh_anti R α t 0 _ _ ha (by positivity : 0 ≤ (r:ℝ)/L)).trans
     have ht:(size z:ℝ) ≤ 4*r:=by exact_mod_cast ambient_size (k-x)
     have hv:=walk_tiny (Q u) (F/L^2) (fun y hy a=> he' _ _ _ ((Nat.cast_le.mpr hy).trans (ht.trans (by gcongr)))) z le_rfl
     have hR:(r:ℝ)/L≤ min 1 ((1+r)/L):= le_min ((div_le_one hL).mpr h) (div_le_div_of_nonneg_right (by linarith only) hL.le)
     calc
       _ ≤ 4*r*(F/L^2) := hv.trans (mul_le_mul_of_nonneg_right ht (by positivity))
       _ = 4*F*(L⁻¹*((r:ℝ)/L)) := by ring
       _ ≤ C*(L⁻¹*min 1 ((1+r)/L)):= by unfold C; gcongr; linarith only [hF]
       _ = _:=rfl
   have hh: L < (r:ℝ):= lt_of_not_ge h
   rw [show rush L r=L⁻¹ from by unfold rush; rw [min_eq_left ((one_le_div hL).mpr (by linarith)),mul_one]]
   obtain ⟨i,hi⟩:=axisEquiv.surjective u; subst u; change sh R α t _ (fleece A _ _ (k,coord i)) ≤ _*L⁻¹
   rw [scalar_lift,sub_eq_add_neg]; apply (sh_add ..).trans
   rw [sh_neg]; let U:= R
   have ht : (r:ℝ)≤L*(4+(r:ℝ)/L):= by field_simp; nlinarith only[hL]
   have hw:= hX k ((r:ℝ)/L) (by rw [separation_comm]; exact ht) (coord i)
   refine (add_le_add hw ((sh_sum ..).trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>2*(F/L)) (fun j _=>?_)))).trans ?_
   · rw [sh_scale]; refine mul_le_mul (wrap_pad _ _ _ _ _ hn) (hX x ((r:ℝ)/L) ?_ _) (sh_nn ..) (by norm_num)
     rw [separation_self, Nat.cast_zero]; positivity
   unfold C; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,Axis]; field_simp; norm_num; nlinarith only [hF]
 · let r:= separation i.1 x; let a:= Q i.2; let z:= lift (i.1-x); unfold bloom lin; apply (sh_sum ..).trans
   refine (sum_le_sum (s:=univ) (g:=fun _=> (r:ℝ)*(F/L^2)) (fun j _=>?_)).trans ?_
   · rw [sh_scale]; exact mul_le_mul (component_cost x i.1 j) (he' i.2 0 j (by simp [Laurent.size]; positivity)) (sh_nn ..) (Nat.cast_nonneg _)
   simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,Axis]; unfold C; push_cast
   change 4*((r:ℝ)*(F/L^2)) ≤ 100*F*((1+(r:ℝ))/L^2)
   field_simp; nlinarith only [hF,mul_nonneg hF (Nat.cast_nonneg (α:=ℝ) r)]
 · let r:= separation i.1 x; let a:= Q i.2; let z:=lift (i.1-x); let D':ℝ:=1+r; have h0 : 0<D':=by unfold D'; positivity
   change sh R α t 0 (quad a z) ≤ _ ; unfold quad; apply (sh_sum ..).trans
   apply le_trans (sum_le_sum (g:=fun _=>∑ _y:Axis,(1+(r:ℝ))^2*(F/L^3)) (s:=univ) (fun j _=>?_))
   · unfold C; change _≤100*F*((1+(r:ℝ))^2/L^3); simp [Axis]; field_simp; nlinarith only [hF]
   apply (sh_sum ..).trans; apply sum_le_sum; intro k _; rw [sh_scale]; have hr : sh R α t 0 (move (move a j) k 0) ≤ F/L^3 := by
       unfold a; rw [h']; apply hP [k,j] (by simp) ((wrap f 0)+x) 0 ?_ i.2; rw [map_zero,zero_add,separation_self,Nat.cast_zero]; positivity
   have hy(a): |(z a:ℝ)| ≤ r:= component_cost x i.1 a
   have hv : |(if j=k then (z j:ℝ) else 0)|≤r := by split_ifs; exact hy j; simp
   have hg : |quadT j k z| ≤ (1+(r:ℝ))^2:=by
      unfold quadT; rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2),div_le_iff₀ (by norm_num : (0:ℝ)<2)]
      apply (abs_sub .. |>.trans ?_); rw [abs_mul]; nlinarith only [mul_le_mul (hy j) (hy k) (abs_nonneg _) (Nat.cast_nonneg (α:=ℝ) _),hv,Nat.cast_nonneg (α:=ℝ) r, sq_nonneg (r:ℝ)]
   exact mul_le_mul hg hr (sh_nn ..) (sq_nonneg _)
 rcases i with ⟨z,i⟩; rw [hf0 z _ hi]
 let r:= separation z x; let y:=lift (z-x); have ht : (size y:ℝ) ≤ 4*r:=by exact_mod_cast ambient_size (z-x)
 change sh R α t 0 (Q i y-Q i 0- lin (Q i) y-quad (Q i) y) ≤ _
 apply (second_tiny (Q i) (R:=size y) (F/L^4) ?_ (by positivity) y le_rfl).trans
 · refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ht 3) (by positivity : 0 ≤ F/L^4)).trans ?_; unfold C
   change _≤ 100*F*((1+(r:ℝ))^3/L^4); field_simp
   have hf : (r:ℝ)^3 ≤ (1+(r:ℝ))^3:= by gcongr; linarith only
   nlinarith only [mul_le_mul_of_nonneg_left hf hF,mul_nonneg hF (show 0 ≤ (r:ℝ)^3 by positivity)]
 intro w hh j k q; rw [hu]; apply hP [q,k,j] (by simp) (wrap f w+x) 0 ?_ i
 rw [add_zero,mul_comm]; refine ((Nat.cast_le.mpr (close_walk w x)).trans (Nat.cast_le.mpr hh)).trans (ht.trans ?_); gcongr
end YM.Trace.Perfect

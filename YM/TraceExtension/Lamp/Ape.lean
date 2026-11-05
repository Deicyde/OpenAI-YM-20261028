import YM.TraceExtension.Lamp.Sox
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
variable {F:∀ w, Peat G (g w)}{Y:∀ w, Gal G (g w)}
def knick (F:∀ w:W,Peat G (g w)): Prop:= Parked (fun w (_x:Link G (g w))=> Kbody (F w)) 0
lemma bright (h:knick F)(i j:Loc G 1)(k:ℕ): Honor (fun w=> bay (F w) i j) k:=by
    obtain ⟨b,C,hb,hC,H⟩:= (show Parked _ _ from h).top
    let a:= b/8; let N:=(1+(2:ℝ)^k/a)^k; have ha: 0<a:=by unfold a; positivity;
    have hv:0 ≤ C * N*cabD k:=by unfold N; have he:=cabD_n (k:=k); positivity
    let V:=C*N*cabD k
    refine ⟨V*countCost (b/2),mul_nonneg hv (count_pos (half_pos hb)).le,fun w x=>?_⟩
    let Z:= (F w); let B(t:Site (g w)):=Kane Z (0,i) (t,j); let p(t:Site (g w))(x:Track):=mode (axes x) (lift t)
    have hs(t:Site (g w)):‖B t‖ ≤ C*Decay b t 0:=by
       have h:= H w (0,i) (t,j)|>.2 0 le_rfl Fin.elim0; simp only [entry,iteratedFDeriv_zero_apply,spanSites, sum_of_isEmpty, Nat.cast_zero,mul_zero, Real.exp_zero,mul_one] at h; rw [decay_comm]; unfold B Kane; simp only[approached,Matrix.map_apply,Complex.norm_real];exact h
    apply Allows.mono (allows_sum (f:=fun i x=> B i*p i x) (s:=univ) (C:=fun i=> V* Decay (b/2) (0:Site (g w)) i) ?_); swap
    · intro i hi; have ht:= sea_mark (k:=k) i x ha 0; simp only [sub_zero] at ht
      apply (cabin (allows_const x (hs i)) ht).mono; rw[decay_comm (b/2)]; unfold Decay; apply le_of_eq; unfold V N a; rw [show -(b/2)*(separation i 0:ℝ)= -b*separation i 0+(4*(b/8)*separation i 0) by ring, Real.exp_add]; ring
    rw [← mul_sum];exact mul_le_mul_of_nonneg_left (decay_count (half_pos hb) _) hv
-- shrink all longs
variable (Q:Tendsto (fun w=>(g w).val) L atTop)
include Q
lemma knock (i:Axis)(m:ℤ)(hp:m≠0) : ∀ᶠ w in L, cell (wrap (g w) (ra i m)) (step i) ≠ 1:=by
    have ht:= roll_hit Q i (ra i m)
    have hz: (ra i m) i=m:=by simp [ra]
    rw [hz] at ht; filter_upwards[ht.eventually_ne (show (-Complex.I)*(m:ℂ)≠0 from mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Int.cast_ne_zero.mpr hp))] with x hx
    intro he; rw[he,sub_self,mul_zero] at hx; exact hx rfl
omit Q in
lemma nearby (i j: Axis)(m:ℤ)(h:i≠j): cell (wrap f (ra i m)) (step j)=1:=by rw[← wrap_step,cell_wrap,(reel_roll f (ra i m)).exp]; simp [mode,mul_ite,axes,reel,ra,h.symm]
lemma bright_z (h:knick F)(hv:∀ w,Contours (F w))(hs:G.Simple)(i j:Loc G 1) : Tendsto (fun w=> ((pitchf (g w):ℂ)⁻¹)^ (2:ℕ)*bay (F w) i j 0) L (𝓝 0):=by
    rcases j with ⟨j,k⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective j
    let T:= (step a:Track)
    refine base0kill (gran Q) T (bright h i (axisEquiv a,k) 3) (fun j hj=> ?_)
    have hj' : (j:ℤ)≠0:= by
        have h:j ≠ 0:=by intro ht; subst j; norm_num at hj
        exact_mod_cast h
    filter_upwards[knock Q a (j:ℤ) hj'] with w hw
    let u:=wrap (g w) (ra a ↑j); let G' := Kane (F w)
    have ht:= Kcup hs (hv w|>.coat) u k
    rw[sum_eq_single a] at ht; swap
    · intro v _ he; rw[show cell u (step v)=1 from nearby _ _ _ he.symm,sub_self,zero_smul]
    swap; · simp
    obtain he:= (smul_eq_zero.mp ht).resolve_left (sub_ne_zero.mpr (Ne.symm hw))
    rw[show (j:ℝ) • T=reel (ra a (j:ℤ)) by rw [ra,reel_z,reel_i]; push_cast;rfl]
    change bay _ _ _ (pitchf _ • _) = _; rw[← bores]; exact congr_fun he (0,i)
def flipH: Signed:= ⟨1,fun _=>true⟩
lemma fee_turn (i:Axis)(q:Cover)(s:Signed) : Tendsto (fun w=>reflectFee s (mon (wrap (g w) q)) i) L (𝓝 (signStar s i)):=by
    unfold reflectFee signStar; split; next e=>
       have ht:= (roll_l Q q (-(step (s.perm i)))).neg; simp_rw[cell_wrap] at ht;exact ht
    next e=> exact tendsto_const_nhds
lemma culled (i j:Loc G 1)(x:Cover)(h: knick F)(hp:∀ w, Contours (F w))(hs:G.Simple){K:Track→ℂ}(he:∀ p, Tendsto (fun w=> neap 2 (bay (F w) i j) 0 p) L (𝓝 (K p))) :
    Tendsto (fun w=>(pitchf (g w):ℂ)⁻¹ ^ (2:ℕ)*shark (F w) i j (wrap (g w) x)) L (𝓝 (K (reel x))):=by
    rcases i with ⟨i,a⟩; obtain ⟨r,rfl⟩:= axisEquiv.surjective i; rcases j with ⟨j,b⟩; obtain ⟨t,rfl⟩:=axisEquiv.surjective j; let i':Loc G 1:=(coord r,a); let j':Loc G 1:=(coord t,b)
    let ρ(w):= reflectFee flipH (mon (wrap (g w) x)) r *reflectFee flipH (mon (wrap (g w) (-x))) t; let V(w):= bay (F w) i' j'
    let t':=pitchf ∘ g
    have hV: Tendsto ρ L (𝓝 1):=by
        have he := (fee_turn Q r x flipH).mul (fee_turn Q t (-x) flipH); simp only [signStar,flipH,ite_true] at he; simpa [ρ,flipH] using! he
    have ht(w): V w (t' w • - reel x)=ρ w * V w (t' w • reel x):=by
       unfold V ρ t'; simp only[Function.comp_apply];rw [← reel_neg, ← bores, ← bores]
       let z:=wrap (g w) x
       have hi := shark_her (hp w) z r t a b flipH
       have hx: flipH.act z= -z:=by
           ext i; change flipH.act z (flipH.perm i)= _; rw [flipH.act_at]; rfl
       rw [hx,neg_neg] at hi; rw [map_neg]; exact hi
    simp_rw[bores]; exact dual_even (gran Q) (bright h _ _ 3) (bright_z Q h hp hs _ _) (he _) ρ hV ht
end YM.Trace.Lamp

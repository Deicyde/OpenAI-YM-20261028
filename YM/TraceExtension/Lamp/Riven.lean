import YM.TraceExtension.Lamp.Cask

/-! # Sym application annihilates degree1 at dial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*}{g:W→Side}{H K:WickL G}{T:Reed G}{L:Filter W}{Y:∀ w, Gal G (g w)}
variable (Q:Tendsto (fun w=>(g w).val) L atTop)
abbrev w0 (F: Funds (Lines G f k))(i j:Loc G k)(p q:Cover):ℂ:= (pitchf f:ℂ)⁻¹ *pier F (wrap f p) (wrap f q) i j
include Q
lemma roll_down (i: Axis)(x y:Cover): Tendsto (fun w=> (pitchf (g w):ℂ)⁻¹*(1-cell (wrap (g w) x+wrap (g w) y) (-step i))) L (𝓝 (Complex.I*((x i:ℂ)+(y i:ℂ)))):=by
    let z:= -(x+y); have ht:= roll_hit Q i z
    unfold z at ht; simp only [map_neg,map_add,Pi.neg_apply,Pi.add_apply,Int.cast_add] at ht
    rw [Int.cast_neg,Int.cast_add,neg_mul_neg] at ht
    apply ht.congr'; filter_upwards with z; congr 2; rw [cell_duality, cell_inverse, cell_inverse, cell_duality]
lemma teat_down (b:Axis)(i j:Loc G k) (p q:Cover):
    Tendsto (fun w=>w0 (f:=g w) (teat G (stampQ (0:Site (g w))) b k) i j p q) L (𝓝 (if i=j then -(Complex.I*((p b:ℂ)+(q b:ℂ))) else 0)):=by
    unfold w0; simp_rw[pitch_teat]; by_cases he:i=j
    · subst j; simp only [↓reduceIte]; apply (roll_down Q b p q|>.neg).congr'; filter_upwards with x; ring
    simp only [he,↓reduceIte,mul_zero]; exact tendsto_const_nhds

lemma pack_b (p q:Cover)(b:Axis)(u v:G.ColorIndex):
    Tendsto (fun w=> w0 (mine G (stampQ (0:Site (g w))) b*mail (1:Config G (g w))) (vac,u) (vac,v) p q) L (𝓝 (if u=v then -Complex.I*(p b:ℂ) else 0)):=by
    unfold w0; simp_rw[packPier]; by_cases he:u=v
    · simp only [he,↓reduceIte]; exact roll_hit Q b p
    simp only [he,↓reduceIte,mul_zero]; exact tendsto_const_nhds
lemma pack_r (p q:Cover)(b:Axis)(i j:Axis)(u v:G.ColorIndex):
    Tendsto (fun w=> w0 (mail (1:Config G (g w))*mine G (stampQ (0:Site (g w))) b) (mood G i u) (mood G j v) p q) L (𝓝 (if b=j ∧ u=v then Complex.I*(q i:ℂ) else 0)):=by
    unfold w0; simp_rw[pickPier]; by_cases he : b=j∧u=v; simp only[he,↓reduceIte]; have h:= roll_down Q i 0 q; simp only[map_zero,zero_add,Pi.zero_apply,Int.cast_zero] at h; exact h
    simp only[he,↓reduceIte,mul_zero]; exact tendsto_const_nhds
lemma pack_d (p q: Cover)(b:Axis)(i j:Axis)(u v:G.ColorIndex):
    Tendsto (fun w=> w0 (deal G (stampQ (0:Site (g w))) b) (mood G i u) (mood G j v) p q) L (𝓝 (if b=j ∧ u=v then -(Complex.I*((p i:ℂ)+(q i:ℂ))) else 0)):=by
    unfold w0;simp_rw[dealP]; by_cases he : b=j ∧ u=v
    · simp only[if_pos he]; apply ((roll_down Q i p q).neg).congr'; filter_upwards with z; ring
    simp only[he,↓reduceIte,mul_zero]; exact tendsto_const_nhds
lemma spin_rill {A:∀ w,Funds (Lines G (g w) k)}(i j:Loc G k)(p q:Cover){a b:ℂ}(h:Tendsto (fun w=> w0 (A w) i j p q) L (𝓝 a))(he:Tendsto (fun w=> w0 (A w) j i q p) L (𝓝 b)): Tendsto (fun w=> w0 (sy (A w)) i j p q) L (𝓝 ((1/2:ℂ)*(a+b))):=by
    apply ((h.add he).const_mul _).congr'; filter_upwards with z; unfold w0; rw[pier_sy]; ring
lemma combine_p (p q:Cover)(b:Axis)(i j:Loc G 0): Tendsto (fun w=> w0 (wG (stampQ 0) b (1:Config G (g w))) i j p q) L (𝓝 0):=by
    rcases i with ⟨i,u⟩; rcases j with ⟨j,v⟩; rw[vac_only i,vac_only j]
    have h:=spin_rill Q (vac,u) (vac,v) p q (pack_b Q p q b u v) (pack_b Q q p b v u)
    have hx:= h.sub ((teat_down Q b (vac,u) (vac,v) p q).const_mul (1/2:ℂ)); rw [show (1/2:ℂ)*_- _=0 from ?_] at hx
    · apply hx.congr'; filter_upwards with w; unfold w0 wG; rw[pier_sub,pier_cash];push_cast;ring
    by_cases h:u=v<;>simp[h,eq_comm]<;> ring
-- vector abstract shrink
variable (b:Axis)(hP:∀ w, Y w∈ rains G (g w)){ε:W→ℝ}(hε:Tendsto ε L (𝓝 0))(hv:∀ w, Testify (0:Site (g w)) (bottom (Y w)) (missY b) 5 (ε w))(hM:CodeM (g:=g) (fun _=>0) (fun w=> Y w∘input G (g w)) 1)(ht:G.Simple)
include hP hv hε hM ht
lemma combine_r (p q:Cover)(i j:Loc G 1): Tendsto (fun w=> w0 (wB (stampQ 0) b (Y w) 1) i j p q) L (𝓝 0):=by
    apply high_filter; intro L' hw
    have hC(w): Cloaked (Y w):=by obtain ⟨h,_⟩:=hP w;exact h
    obtain ⟨K,hK⟩:=flamed L' hM hC
    have he:=Q.mono_left hw; let B(w):= tidal (Y w) 1- mail (1:Config G (g w))*mine G (stampQ 0) b - deal G (stampQ 0) b
    have hh(p q:Cover)(i j:Loc G 1): Tendsto (fun w=> w0 (B w) i j p q) (↑L':Filter W) (𝓝 (if i=j then Complex.I*(p b:ℂ) else 0)):=by
        have hm:= wick_span he hM hC ht hK i j p q; rcases i with ⟨i,u⟩; rcases j with ⟨j,v⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective i; obtain ⟨j,rfl⟩:= axisEquiv.surjective j
        let I:=mood G i u; let J:=mood G j v; let r:= reel p; let s:=reel q
        have hx:= (hm.sub (pack_r he p q b i j u v)).sub (pack_d he p q b i j u v)
        convert hx using 1
        · funext x; unfold B w0; rw [pier_sub,pier_sub,tide_dot _ _ _ _ (hP x),mul_sub,mul_sub]; rfl
        congr 1; rw [show K (axisEquiv i,u) (axisEquiv j,v) (reel p,reel q)= _ from analytic_full b i j u v p q hP hK hv (hε.mono_left hw) (know he hC ht hM hK)]
        simp only[Prod.mk.injEq,Equiv.apply_eq_iff_eq]; split_ifs <;> ring
    have hg:= (spin_rill he _ _ _ _ (hh p q i j) (hh q p j i)).add ((teat_down he b i j p q).const_mul (1/2:ℂ))
    convert hg using 1
    · funext x; unfold wB w0; rw[pier_add,pier_cash]; push_cast; change ((pitchf _ :ℂ)⁻¹ * (pier (sy (B x)) _ _ i j+ _)) = _; ring
    congr 1; by_cases h:i=j<;>simp[h,eq_comm]<;> ring
end YM.Trace.Lamp

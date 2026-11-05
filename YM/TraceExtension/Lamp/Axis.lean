import YM.TraceExtension.Lamp.Ape
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
variable {F:∀ w, Peat G (g w)}
abbrev Reed (G:Gauge) := Loc G 1→Loc G 1→Track→ℂ
structure Campus (K:Reed G): Prop where
    move (s:Signed)(x:Cover)(a b:Axis)(p q:G.ColorIndex): K (mood G (s.perm a) p) (mood G (s.perm b) q) (reel (s.act x))= signStar s a*signStar s b*K (mood G a p) (mood G b q) (reel x)
    normQ(a b:Loc G 1)(t u:ℝ)(x y:Track) : K a b (t • x+u • y)= (t:ℂ)^ (2:ℕ)*K a b x + (u:ℂ)^ (2:ℕ)* K a b y + (t:ℂ)*(u:ℂ)*(K a b (x+y)-K a b x-K a b y)
    kill (x:Cover)(i:Loc G 1)(c:G.ColorIndex): ∑ j:Axis,(x j:ℂ)*K i (mood G j c) (reel x)=0
structure Shine (L:Filter W)(K:Reed G)(F:∀ w:W,Peat G (g w)):Prop where
    tracks(i j:Loc G 1)(x:Track):Tendsto (fun w=> neap 2 (bay (F w) i j) 0 x) L (𝓝 (K i j x))
lemma shine (L: Ultrafilter W)(h: knick F):∃ K, Shine ↑L K F :=by
    have hx(i j:Loc G 1)(x:Track):∃ q:ℂ,Tendsto (fun w=> neap 2 (bay (F w) i j) 0 x) (↑L) (𝓝 q):=by
       obtain ⟨C,hC,H⟩:= (bright h i j 2).top
       refine whirl_fee _ _ ⟨_,?_,Eventually.of_forall fun w=> norm_neap (H w 0) le_rfl⟩; positivity
    choose K hp using hx; exact ⟨K,⟨hp⟩⟩
lemma arc_sec (F:X→ℂ)(x y:X)(a b:ℝ): neap 2 F 0 (a • x+b • y) = (a:ℂ)^ (2:ℕ)*neap 2 F 0 x+(b:ℂ)^(2:ℕ)*neap 2 F 0 y+(a:ℂ)*(b:ℂ)*(neap 2 F 0 (x+y)-neap 2 F 0 x-neap 2 F 0 y):=by
    simp only [neap2,map_add,map_smul,_root_.add_apply,_root_.smul_apply,Complex.real_smul]; ring
lemma shines [L.NeBot] (Q:Tendsto (fun w=>(g w).val) L atTop) {K:Reed G}(h:knick F)(hp: Shine L K F)(hv:∀ w,Contours (F w))(hs:G.Simple): Campus K:=by
    have he(i j x):= culled Q i j x h hv hs (hp.tracks i j); refine ⟨fun s x a b p q=>?_,fun i j u v x y=> ?_,fun x i k=>?_⟩
    · apply tendsto_nhds_unique (he _ _ (s.act x))
      apply (((fee_turn Q a (-(s.act x)) s).mul (fee_turn Q b (s.act x) s)).mul (he _ _ x)).congr'; filter_upwards with w; rw [map_neg,← wrap_signed]; have hx:= shark_her (hv w) (wrap (g w) x) a b p q s
      rw [show shark (F w) (mood _ _ _) (mood _ _ _) (s.act (wrap (g w) x))= _ from hx]; unfold mood; ring
    · apply tendsto_nhds_unique (hp.tracks i j (u • x+v • y)); have hx:=hp.tracks i j; apply ((((hx x).const_mul _).add ((hx y).const_mul _)).add ((((hx (x+y)).sub (hx x)).sub (hx y)).const_mul _)).congr'; filter_upwards with w; exact (arc_sec (bay (F w) i j) ..).symm
    have hh:= tendsto_finsetSum (s:=univ) (fun j (_:j∈univ)=> (roll_hit Q j x).mul (he i (mood G j k) x))
    have ht(w:W): ∑ j:Axis, ( (pitchf (g w):ℂ)⁻¹ * (1-cell (wrap (g w) x) (step j)))*((pitchf (g w):ℂ)⁻¹ ^(2:ℕ)*shark (F w) i (mood G j k) (wrap (g w) x))=0:=by
       have hu:= congr_fun (Kcup hs (hv w|>.coat) (wrap (g w) x) k) (0,i); rw[Finset.sum_apply] at hu
       let z:ℂ:=(pitchf (g w):ℂ)⁻¹; let p:=wrap (g w) x
       have hz: ∑ j:Axis,(1-cell p (step j))*shark (F w) i (coord j,k) p=0:=hu
       rw [show ∑ j:Axis,_= z^ (3:ℕ)*∑ j:Axis,(1-cell p (step j))*shark (F w) i (coord j,k) p from ?_,hz,mul_zero]; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; unfold z p mood; ring
    have hW : ∑ j:Axis, (-Complex.I*(x j:ℂ))*K i (mood G j k) (reel x)=0:=by
        apply tendsto_nhds_unique hh; exact tendsto_const_nhds.congr' (f₁:=fun _=>0) (Eventually.of_forall (fun i=> (ht i).symm))
    simp_rw [mul_assoc] at hW; rw [← mul_sum] at hW; exact (mul_eq_zero.mp hW).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
lemma signP(a b:Axis): signStar (soleSpin a) b=if a=b then -1 else 1:=by simp[signStar,soleSpin]
lemma rollingCover (s:Signed)(p:Axis): s.act (step p:Cover)=if s.flip p then -(step (s.perm p)) else step (s.perm p):=by funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [s.act_at]; by_cases h : i=p <;> cases hp : s.flip p <;> simp [*]
lemma turn_mask (s:Signed)(x:Cover): reel (s.act x)=s.act (reel x):=by funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; unfold reel; rw [s.act_at,s.act_at]; split<;>simp
lemma permTrip (a b c d:Axis)(h:a≠b)(he:c≠d):∃ p:Equiv.Perm Axis,p a=c ∧ p b=d:=by
    let r:=Equiv.swap a c; let s:= r.trans (Equiv.swap (r b) d)
    have ht:r a=c:= Equiv.swap_apply_left ..; have hp:r b ≠ c:=by rw[← ht]; exact r.injective.ne h.symm
    exact ⟨s,(show Equiv.swap (r b) d (r a)=c by rw [ht,Equiv.swap_apply_of_ne_of_ne hp.symm he]),Equiv.swap_apply_left ..⟩

variable {K:Reed G} (h:Campus K)
def tickt (K:Reed G)(p q:G.ColorIndex):ℂ:=K (coord 0,p) (coord 0,q) (step 1)
include h
lemma Campus.scaleM (i j:Loc G 1)(x:Track)(u:ℝ) : K i j (u • x)= (u:ℂ)^(2:ℕ)* K i j x:=by simpa using h.normQ i j u 0 x 0
lemma Campus.evenM (i j:Loc G 1)(x:Track):K i j (-x)=K i j x:=by simpa using Campus.scaleM h i j x (-1)
lemma Campus.diag (a b:Axis)(i j:G.ColorIndex)(s:Axis) : K (coord a,i) (coord b,j) (step s)= if a=b ∧ a≠s then tickt K i j else 0:=by
    by_cases hab:a=b
    · subst b; by_cases ha:a=s
      · subst s; simp only [ne_self_iff_false,and_false,↓reduceIte]
        have hx:= h.kill (step a) (coord a,i) j; simpa [apply_ite ((↑):ℤ→ℂ),ite_mul,reel_i,mood] using hx
      rw [if_pos ⟨rfl,ha⟩]; obtain ⟨p,h0,h1⟩:= permTrip 0 1 a s (by decide) ha; have he := h.move (platey p) (step 1) 0 0 i j
      simp only [turn_mask,reel_i,natural_step,h1] at he; simp only[signStar,platey,h0] at he; simpa [tickt,mood] using he
    have hx := soleSpin a
    have ht:= h.move (soleSpin a) (step s) a b i j; rw [turn_mask,reel_i] at ht; simp_rw [signP] at ht
    rw [ite_true,if_neg hab] at ht; rw [if_neg (fun e=>hab e.1)]; change K (coord a,i) (coord b,j) ( (soleSpin a).act _) = _ at ht
    have hp: K (coord a,i) (coord b,j) ( (soleSpin a).act (step s))= K (coord a,i) (coord b,j) (step s):=by
       by_cases hv:a=s
       · rw[hv,swish_axis,Campus.evenM h]
       rw[keep_axis _ _ hv]
    rw[hp, mul_one,neg_one_mul] at ht; unfold mood at ht; linear_combination ht/2
lemma Campus.cross_v (a b x y:Axis)(i j:G.ColorIndex)(_hp:x≠y)(hz:b≠x)(ht:b≠y)(he:a≠b): K (coord a,i) (coord b,j) (step x+step y) =0:=by
    have hh:= h.move (soleSpin b) (step x+step y) a b i j
    rw [turn_mask,reel_be,reel_i,reel_i,(soleSpin b).act_add,keep_axis b x hz,keep_axis b y ht,signP,signP,if_neg he.symm,if_pos rfl,one_mul, neg_one_mul] at hh
    change K (coord a,i) (coord b,j) _ = - K (coord a,i) (coord b,j) _ at hh
    linear_combination hh /2
lemma Campus.diag_add (a x y:Axis)(i j:G.ColorIndex)(he:x≠y):
    K (coord a,i) (coord a,j) (step x+step y)= K (coord a,i) (coord a,j) (step x)+K (coord a,i) (coord a,j) (step y):=by
    let F:=K (mood G a i) (mood G a j)
    have hx:= h.move (soleSpin y) (step x+step y) a a i j
    rw[turn_mask,reel_be,reel_i,reel_i,(soleSpin y).act_add,keep_axis y x he.symm,swish_axis,signP] at hx
    have hh : F (step x+ -step y)=F (step x+step y):=by split at hx<;> simp only[neg_mul, mul_neg, neg_neg,one_mul] at hx<;> exact hx
    have ht:= h.normQ (mood G a i) (mood G a j) 1 (-1) (step x) (step y)
    change _ = _ at ht
    rw [neg_one_smul,one_smul,show K _ _ (step x+ -step y)=_ from hh] at ht
    push_cast at ht; change F _= (1:ℂ)^2*F _+ (-1)^ (2:ℕ)*F _+1*(-1)*(F _-F _-F _) at ht
    change F _=F _+F _; linear_combination ht/2
lemma Campus.pall (a x y:Axis)(i j:G.ColorIndex)(_he:x≠y): K (coord a,i) (coord x,j) (step x+step y)= -K (coord a,i) (coord y,j) (step x+step y):=by
    have hx:=h.kill (step x+step y) (coord a,i) j
    simp only [reel_be,reel_i,Pi.add_apply,Int.cast_add,add_mul, Finset.sum_add_distrib] at hx
    exact eq_neg_of_add_eq_zero_left (by simpa [apply_ite ((↑):ℤ→ℂ),ite_mul,mood] using hx)
lemma Campus.nickM (a b x y:Axis)(i j:G.ColorIndex)(_he:x≠y)(h₁:a ≠ b)(h₂:a≠x)(h₃:a≠y): K (coord a,i) (coord b,j) (step x+step y)=0:=by
    have hh:= h.move (soleSpin a) (step x+step y) a b i j
    rw[turn_mask,reel_be,reel_i,reel_i,(soleSpin a).act_add,keep_axis a x h₂,keep_axis a y h₃, signP,signP,if_pos rfl,if_neg h₁,mul_one,neg_one_mul] at hh
    change K (coord a,i) (coord b,j) (step x+step y)= - K (coord a,i) (coord b,j) _ at hh; linear_combination hh/2
-- provide full step-span
abbrev dotK (p:Track):ℝ:= dotProduct p p
def MaxwellK (p:Track)(a b:Axis):ℂ:= (dotK p :ℂ)*(if a=b then 1 else 0)-(p a : ℂ)*(p b:ℂ)
omit h in
lemma maxdi (a b i j:Axis)(he:i≠j)(s t:ℝ): MaxwellK (s • step i + t •step j) a b=
   ((s:ℂ)^ (2:ℕ)+(t:ℂ)^ (2:ℕ))*(if a=b then 1 else 0) - ((if a=i then (s:ℂ) else 0)+(if a=j then (t:ℂ) else 0))*((if b=i then (s:ℂ) else 0)+(if b=j then (t:ℂ) else 0)) :=by
    have hv(f g:Axis) : dotProduct (step f:Track) (step g)= if f=g then 1 else 0:=by rw[step]; by_cases h:f=g<;> simp [step,h,eq_comm]
    unfold MaxwellK dotK; rw [add_dotProduct,dotProduct_add,dotProduct_add]; simp only [smul_dotProduct,dotProduct_smul,hv]; simp only[he, he.symm, ↓reduceIte]
    push_cast; simp [step_apply,mul_ite,apply_ite ((↑):ℝ→ℂ)]; ring
omit h in
lemma max_one_i (a b i:Axis)(s:ℝ): MaxwellK (s • step i) a b = if a=b ∧ a≠i then (s:ℂ)^ (2:ℕ) else 0:=by
    let p:=(step i:Track); have ht : dotProduct p p=1:=by simp [p,step]
    unfold MaxwellK dotK; change ((dotProduct (s • p) (s • p):ℝ):ℂ)* _ - _=_; rw[smul_dotProduct,dotProduct_smul,ht]; simp only [smul_eq_mul]; push_cast; simp only[Pi.smul_apply,step_apply]; split_ifs<;> first| contradiction| simp_all <;> ring
lemma Campus.full (a b i j:Axis)(w t:G.ColorIndex)(s u:ℝ) : K (coord a,w) (coord b,t) (s • step i+ u •step j)= tickt K w t * MaxwellK (s • step i + u • step j) a b:=by
    by_cases he:i=j
    · subst j; rw[← add_smul,Campus.scaleM h,Campus.diag h,max_one_i];split<;>first| ring|simp
    rw [h.normQ,maxdi _ _ _ _ he]
    by_cases hh:a=b
    · subst b; rw [Campus.diag_add h _ _ _ _ _ he,Campus.diag h,Campus.diag h]
      by_cases hp:a=i
      · subst a; simp [he]; ring
      by_cases hx:a=j
      · subst a; simp [hp];ring
      simp [hp,hx];ring
    by_cases ha:a=i ∨ a=j
    · by_cases hb:b=i ∨ b=j
      · rcases ha with ha|ha<;>subst a<;>rcases hb with hb|hb<;>subst b<;> (first| contradiction| skip)
        · have hx: K (coord i,w) (coord j,t) (step i+step j)= -K (coord i,w) (coord i,t) (step i+step j):= by rw [Campus.pall h i i j w t he,neg_neg]
          rw[hx,Campus.diag_add h _ _ _ _ _ he];simp_rw[Campus.diag h i i w t  i,Campus.diag h i i w t j,Campus.diag h i j]; simp[he,Ne.symm he];ring
        rw [Campus.pall h _ _ _ _ _ he,Campus.diag_add h _ _ _ _ _ he]; simp_rw [Campus.diag h j j w t i,Campus.diag h j j w t j, Campus.diag h j i]; simp [he,Ne.symm he];ring
      push Not at hb;rw[Campus.cross_v h _ _ _ _ _ _ he hb.1 hb.2 hh];simp [Campus.diag h a b, hh,hb]
    push Not at ha; rw[Campus.nickM h _ _ _ _ _ _ he hh ha.1 ha.2]; simp [Campus.diag h a b,hh,ha]
end YM.Trace.Lamp

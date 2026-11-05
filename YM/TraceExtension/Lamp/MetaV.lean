import YM.TraceExtension.Lamp.Chit
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {W:Type*}{g:W→Side}{L:Filter W}
def xylo (V:WildM G f k l)(i:Loc G k)(j:Loc G l)(p: Site f)(h:Loc G 1):ℂ:= dotProduct (relay 0 i) (seat V (relay p h)*ᵥ relay 0 j)
variable {F:(w:W)→ WildM G (g w) k k} (Q:Tendsto (fun w=>(g w).val) L atTop)
include Q
lemma shock_up (h:∀ w,Tempo (F w))(K:∀ i j x y, Tendsto (fun w=> w0 (F w 0) i j x y) L (𝓝 0))(i j:Loc G k)(a: Axis)(u:G.ColorIndex): Tendsto (fun w=> xylo (F w) i j (step a) (mood G a u)) L (𝓝 0):=by
    let S (w:W):Site (g w):=step a
    let V(w):= seat (jerk G (g w) k) (relay (S w) (vac,u)); let U(w):= approached (F w 0)
    let μ(w):=(pitchf (g w):ℂ)⁻¹; let p:=mood G a u;let q w:=1-cell (S w) (step a)
    let R(w):= μ w*dotProduct (relay 0 i) ((V w*U w)*ᵥrelay 0 j); let G'(w):= μ w*dotProduct (relay 0 i) ((U w*V w)*ᵥrelay 0 j)
    let T w:= xylo (F w) i j (step a) p
    have ht : ∀ w, μ w*q w*T w=R w-G' w:=by
        intro w
        have he:seat (F w) (relay (S w) p)=(seat (F w) (relay (S w) (coord a,u))):=rfl
        have hf ww (hw:ww ≠ a): cell (S w) (step ww)=1:=by rw [show S w=wrap (g w) (ra a 1) by simp [ra,S]]; exact nearby a ww 1 hw.symm
        have hh:= chi_price (h w) (S w) u a hf; unfold T xylo
        rw [mul_assoc,← smul_eq_mul (q w) _,← dotProduct_smul, ← smul_mulVec]
        change μ w* dotProduct _ (( (_:ℂ) • seat _ (_)) *ᵥ _) =_
        rw [show q w • seat (F w) (relay (step a) p) = _ from hh, sub_mulVec,dotProduct_sub,mul_sub]
    let hu(v:G.ColorIndex) (p:Loc G k):ℂ:= ↑( (G.ad (tuneV u) (tuneV p.2)) v)
    let FY(w)(p: Loc G k):= fun v:G.ColorIndex=> relay (S w) (p.1,v)
    have hz(w)(p:Loc G k): V w *ᵥ (relay (0:Site (g w)) p)= ∑ v:G.ColorIndex,(hu v p) • FY w p v:=by unfold V FY; rw[shocks]; simp only[add_zero];rfl
    have hp : Tendsto R L (𝓝 0):=by
       let H(v:G.ColorIndex)(w:W):= -(hu v i)*w0 (F w 0) (i.1,v) j 0 (step a)
       have hh(w): R w=∑ v,H v w:=by
          unfold R; rw [← Matrix.mulVec_mulVec]; let A:= relay (0:Site (g w)) i
          have h(X:Phase (Lines G (g w) k)): A ⬝ᵥ (V w *ᵥ X)= -((V w*ᵥ A) ⬝ᵥ X):=by rw[dotProduct_mulVec,← mulVec_transpose, show (V w)ᵀ= -V w from pear_sign _, neg_mulVec, neg_dotProduct]
          rw [show dotProduct (relay (0:Site (g w)) i) _=_ from h (U w *ᵥ relay 0 j)]
          unfold A
          rw [hz, sum_dotProduct, ← Finset.sum_neg_distrib,Finset.mul_sum];
          refine Finset.sum_congr rfl fun t _=>?_ ; rw[smul_dotProduct];simp only[H,w0,FY,pier,U,map_zero,wrap_step,smul_eq_mul, μ,S];ring
       rw [funext hh]; have hd:=tendsto_finsetSum univ fun x (_:x∈univ) => (K (i.1,x) j 0 (step a)).const_mul (-(hu x i)); simp only[mul_zero,sum_const_zero] at hd;exact hd
    have hg:Tendsto G' L (𝓝 0):=by
       let H(v:G.ColorIndex)(w:W):= (hu v j)*w0 (F w 0) i (j.1,v) (step a) 0
       have hh(w): G' w=∑ v,H v w:=by
           unfold G'; rw [← mulVec_mulVec,hz,mulVec_sum,dotProduct_sum,Finset.mul_sum]; refine sum_congr rfl fun v _=>?_ ; rw[mulVec_smul,dotProduct_smul];simp only[H,w0,FY,pier,U,map_zero,wrap_step,smul_eq_mul,μ,S];ring
       rw [funext hh]; have hd:= tendsto_finsetSum univ fun x (_:x∈univ)=> (K i (j.1,x) (step a) 0).const_mul (hu x j); simp only[mul_zero,sum_const_zero] at hd;exact hd
    have hv:Tendsto (μ*q) L (𝓝 (-Complex.I)):=by have hx:=roll_hit Q a (step a); simp only[wrap_step,step_apply, ↓reduceIte,Int.cast_one,mul_one] at hx; exact hx
    have hx:=hv.eventually_ne (show -Complex.I≠0 from neg_ne_zero.mpr Complex.I_ne_zero)
    have hd := (hp.sub hg).div hv (neg_ne_zero.mpr Complex.I_ne_zero); rw [sub_zero,_root_.zero_div] at hd; apply hd.congr'; filter_upwards[hx] with w hw; change (R w-G' w)/ (μ w*q w)=T w; rw [← ht w]; change _ / (μ w*q w)=T w; rw [mul_comm _ (T w)]; exact mul_div_cancel_right₀ _ hw
end YM.Trace.Lamp

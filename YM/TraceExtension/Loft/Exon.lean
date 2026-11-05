import YM.TraceExtension.Loft.Peaks
set_option autoImplicit false
/-!
# Absolute Infrared force. Residual kernels heat dimension ≥2. Statements
order widths purchased after mass compact cutoff; bounds sent independent. -/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{G:Gauge}{g:W→Side}{q:Clip}{k m n:ℕ}{σ A C D B ε L δ M:ℝ}
variable {F:∀ w, WildM G (g w) k k}{L':Filter W} (h:Oil L' F)(a:Fslot G)(p:Land)(i j:Loc G k)
include h
-- floret scales arbitrary not anchored w
lemma wcap (v:Fin m→ Fslot G)(u:Backs m)(hp:m ≤ 2)(he:v=(fun _=>a)):∃ C:ℝ,0 ≤ C ∧ ∀ δ:ℝ,0<δ → ∀ᶠ w in L',∀ x:Track,∀ T:ℝ, δ≤ T→ T≤ furthest → ‖x‖ ≤ T →
      Allows 3 (fun t:ℝ=> carb 0 (F w) i j v ((((0,x),-x):Backs m)+ t • T • u)) 0 (C*T^(2-m)):=by
    let X(w):=carb 0 (F w) i j v; obtain ⟨C,hC,H⟩:=(carb_cap (g:=g) (p:=v) i j (m:=3) (h.jets.tada hp)).top
    obtain ⟨D,hD,K⟩:=floret (X:=Backs m) (C:= (1:ℝ)) hC zero_le_one furthest_pos 1 ‖u‖ zero_le_one (norm_nonneg _) (by omega:2-m ≤ 3)
    refine ⟨D,hD,fun δ hδ=>?_⟩; have hx: ∀ᶠ w in L',∀ n:ℕ,n< 2-m → ‖iteratedFDeriv ℝ n (X w) 0‖ ≤ δ^(2-m-n):=by
        subst v
        clear H u K
        interval_cases m
        · have he:= h.turn i j; filter_upwards [he.1.eventually (ball_mem_nhds (0:ℂ) (pow_pos hδ 2)), he.2.eventually (ball_mem_nhds 0 hδ)] with w hs hx n hn
          interval_cases n
          · rw[norm_iteratedFDeriv_zero]; have hh: carb 0 (F w) i j (![]:Fin 0→_)=X w:=by unfold X; congr; exact Subsingleton.elim ..
            rw [← hh]; exact (show ‖carb 0 (F w) i j (![]:Fin 0→_) 0‖< _ from by simpa [mem_ball,dist_eq_norm] using hs).le
          have hh: ‖iteratedFDeriv ℝ 1 (X w) 0‖ = ‖fderiv ℝ (X w) 0‖:= norm_iteratedFDeriv_one ..
          rw[hh, show (2-0-(0+1):ℕ)=1 by omega,pow_one]; apply le_of_lt
          rw[show X w=carb 0 (F w) i j (![]:Fin 0→_) from ?_]; swap; · unfold X; congr; exact Subsingleton.elim ..
          simpa [mem_ball] using hx
        · filter_upwards [(h.hat i j a).eventually (ball_mem_nhds 0 hδ)] with w hx n hn; interval_cases n
          rw[norm_iteratedFDeriv_zero, show X w=carb 0 (F w) i j (![a]: Fin 1→_) from ?_]; swap; · unfold X; congr; funext i; fin_cases i; rfl
          simpa [mem_ball] using (show dist (carb 0 (F w) _ _ _ 0) 0 ≤ δ from le_of_lt hx)
        exact Eventually.of_forall fun w n hn=>by omega
    filter_upwards [hx] with w hx x T ht hb hv
    have hT:=hδ.trans_le ht
    refine K _ _ _ T hT hb ?_ ?_ (H w) ?_
    · rw [mul_one]; simp only [Prod.norm_def,norm_zero,norm_neg,max_le_iff]; exact ⟨⟨hT.le,hv⟩,hv⟩
    · rw[norm_smul,Real.norm_of_nonneg hT.le]
    intro i hi; rw[one_mul]; exact (hx i hi).trans (pow_le_pow_left₀ hδ.le ht _)
lemma dots1 (u v:Track): ∃ C:ℝ,0 ≤ C ∧∀ d:ℝ,0<d → ∀ᶠ w in L',∀ x:Track,∀ T:ℝ,d≤T→ T≤furthest→ ‖x‖ ≤ T →
    Allows 3 (fun t:ℝ=> carb 0 (F w) i j (![a]:Fin 1→_) ((![t • T • u],x+t • T • v),-x)) 0 (C*T):=by
    obtain ⟨C,hC,H⟩:= wcap h a i j (![a]:Fin 1→_) ((![u],v),0) (by decide) (funext fun i=> by fin_cases i; rfl)
    refine ⟨_,hC,fun x hx=>?_⟩; filter_upwards [H x hx] with w hw y T hy hp hv; have ht:=hw y T hy hp hv; rw[show (2-1:ℕ)=1 by rfl,pow_one] at ht; apply ht.germ (Eventually.of_forall (fun t=>?_)); dsimp only; congr 1
    refine Prod.ext (Prod.ext ?_ rfl) (by simp); ext1 k; fin_cases k; simp
lemma dots2 (p:Land):∃ C:ℝ,0 ≤ C ∧∀ d:ℝ,0<d→ ∀ᶠ w in L',∀ x:Track,∀ T:ℝ,d≤T→ T≤furthest → ‖x‖≤ T → Allows 3 (fun t:ℝ=>carb 0 (F w) i j (![a,a]:Fin 2→_) ((t • T • p,x),-x)) 0 C:=by
    obtain ⟨C,hC,H⟩:=wcap h a i j _ ((p,0),0) (by decide) (show (![a,a]:Fin 2→_)=(fun _=>a) from funext fun i=> by fin_cases i <;>rfl)
    refine ⟨_,hC,fun d hd=>?_⟩; filter_upwards[H d hd] with w hw x T hx ht hp; simpa using hw x T hx ht hp
include a
lemma dots0 (p q:Track):∃ C:ℝ,0≤ C ∧∀ d:ℝ,0<d→ ∀ᶠ w in L',∀ x:Track,∀ T:ℝ,d≤ T → T≤furthest → ‖x‖ ≤ T→ Allows 3 (fun t:ℝ=> carb 0 (F w) i j (![]:Fin 0→_) ((![],x+(t • T • p+t • T • q)),-x)) 0 (C*T^2):=by
    obtain ⟨C,hC,H⟩:= wcap h a i j (![]:Fin 0→_) ((0,p+q),0) (by decide) (Subsingleton.elim ..)
    refine ⟨_,hC,fun d hd=>?_⟩; filter_upwards [H d hd] with w hw x T hx ht hp; apply (hw x T hx ht hp).germ (Eventually.of_forall (fun t=>?_)); dsimp only; congr 1
    exact Prod.ext (Prod.ext (Subsingleton.elim ..) (by simp [smul_add])) (by simp)
lemma noting {V:Coast k G W}(hp: Sand V) :∃ C:ℝ,0 ≤ C ∧∀ d:ℝ,0 < d→ ∀ᶠ w in L',∀ (x:Site (g w))(μ:ℝ),d ≤ μ→ μ≤ 1 → let z:=peakT x μ;
    Allows 3 (fun t:ℝ=> moss (summitM (V w) μ).back (F w) (sip x) a i j (t • z • p)) 0 (C*(z^ (2:ℕ))⁻¹):=by
    obtain ⟨C,hC,H⟩:=dots1 h a i j (p 1) (p 0); obtain ⟨D,hD,h'⟩:=dots1 h a i j (p 0) (p 1); obtain ⟨E,hE,M⟩:=dots2 h a i j p; obtain ⟨R,hR,N⟩:=dots0 h a i j (p 0) (p 1)
    obtain ⟨A,hA,K⟩:= peaks hp a (p 0) (p 1) (n:=3) j i g
    let c:=cabD 3; have hc:0 ≤ c:=cabD_n
    refine ⟨E*A*c+C*A*c+D*A*c+R*A*c,by positivity,fun d hd=>?_⟩
    filter_upwards [H d hd,h' d hd, M d hd,N d hd] with w h1 h2 h3 h4 x μ hx ht; intro z
    let y:=sip x; have hL:0<μ:= hd.trans_le hx; have hy:μ≤ z:=le_add_of_nonneg_left (orbit_nonneg _); have hz:0<z:= hL.trans_le hy; have hh: z≤furthest:= (add_le_add (orbit_boundary _ (sip_n x)) ht).trans_eq (add_comm ..); have hk: ‖y‖≤z:= (orbit_at _).trans (le_add_of_nonneg_right hL.le)
    obtain ⟨ha,hb,hp,he⟩:=K w x μ ⟨hL,ht⟩; have hv:= hx.trans hy
    refine Allows.mono (C:=((c*E*(A*(z^2)⁻¹)+ c*(C*z)*(A*(z^3)⁻¹))+c*(D*z)*(A*(z^3)⁻¹))+ c*(R*z^2)*(A*(z^4)⁻¹)) ?_ ?_
    · exact (((cabin (h3 y z hv hh hk) ha).add (cabin (h1 y z hv hh hk) hb)).add (cabin (h2 y z hv hh hk) hp)).add (cabin (h4 y z hv hh hk) he)
    apply le_of_eq; field_simp <;> ring
end YM.Trace.Loft

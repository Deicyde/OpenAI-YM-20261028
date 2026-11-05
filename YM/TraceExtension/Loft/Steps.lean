import YM.TraceExtension.Loft.Exon
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{G:Gauge}{g:W→Side}{q:Clip}{k m n:ℕ}{σ A C D B ε L δ M:ℝ}
variable {F:∀ w, WildM G (g w) k k}{L':Filter W} (h:Oil L' F)(a:Fslot G)(p:Land)
variable {U:Coast k G W}(hp:Sand U)(Q:Tendsto (fun w=>(g w).val) L' atTop)
include h hp
lemma arc_a (i j:Loc G k) :∃ A:ℝ, 0 ≤ A ∧ ∀ (δ:ℝ), 0 < δ → ∀ (μ:W→ℝ), (∀ w,δ ≤ μ w∧ μ w≤1)→ ∀ A' σ, 0<σ → (∀ w,Skew (summitM (U w) (μ w)).back σ A')→ ∀ᶠ w in L',∀ x:Site (g w),
    let z:=peakT x (μ w); let V:=moss (summitM (U w) (μ w)).back (F w) (sip x) a i j;
    ‖neap 3 V 0 p‖ ≤ A* (z^5)⁻¹:=by
    obtain ⟨C,hC,H⟩:= noting h a p i j hp
    refine ⟨_,mul_nonneg (show 0≤ ( (Nat.factorial 3):ℝ)⁻¹ by positivity) hC,fun δ hd μ ht A' σ hx hf=>?_⟩
    obtain ⟨D,hD,K⟩:= (honor_sq h hf hx i j a (n:=3)).top
    filter_upwards[H δ hd] with w hw x; intro z V
    have he:= (ht w).1; have hz:0 < z:= add_pos_of_nonneg_of_pos (orbit_nonneg _) (hd.trans_le he); have hh:= norm_neap (p:= (1:ℝ)) (hw x (μ w) he (ht w).2) le_rfl
    have ha: ContDiffAt ℝ ω V 0:= (shunt_a (sip x) 0 (K w (sip x,0))).analytic
    have hs: z^ (3:ℕ) * ‖neap 3 V 0 p‖ ≤ (((Nat.factorial 3):ℝ)⁻¹)* (C*(z^2)⁻¹):=by
       have he: neap 3 (fun t:ℝ=> V (t • z • p)) 0 1=z^ (3:ℕ) • neap 3 V 0 p:=by simp_rw[← neap_tide]; rw[← chord_n (0:Land) (z • p) 3 ha]; simp
       rw[he,norm_smul,Real.norm_of_nonneg (pow_nonneg hz.le _),norm_one, one_pow,mul_one] at hh; exact hh
    refine (le_div_iff₀ (pow_pos hz 3)).mpr ((mul_comm ..).trans_le hs) |>.trans_eq ?_; field_simp
include Q
lemma arc_r : ∃ A:ℝ,0 ≤ A ∧ ∀ (δ:ℝ), 0 < δ→ ∀ (μ:W→ℝ), (∀ w, δ ≤ μ w ∧ μ w≤1) → ∀ A' σ, 0<σ → (∀ w,Skew (summitM (U w) (μ w)).back σ A')→ ∀ᶠ w in L',
    ‖neap 3 (Pond (F w) a (summitM (U w) (μ w)).back) 0 p‖≤ A*(μ w)⁻¹:=by
    choose C hC H using (fun i j=>arc_a h a p hp i j)
    let c:=∑ i, ∑ j,C i j; have hc: 0 ≤ c:=sum_nonneg fun i _=>sum_nonneg fun j _=>hC i j
    let a':ℝ:=2*6^4/(2*Real.pi)^4; have ha':0 ≤ a':=by unfold a'; positivity
    refine ⟨c*a',by positivity,fun δ hδ μ ht A' σ hs hy=>?_⟩
    let V i:= (summitM (U i) (μ i)).back
    have hh:∀ᶠ w in L',∀ i j (x:Site (g w)), ‖neap 3 (moss (V w) (F w) (sip x) a i j) 0 p‖≤ C i j * ((peakT x (μ w))^5)⁻¹ := eventually_all.mpr fun i=> eventually_all.mpr fun j=> H i j δ hδ μ ht A' σ hs hy
    filter_upwards [hh,(gran Q).void.eventually (ge_mem_nhds hδ)] with w hw hx
    let N:=Wsc (g w); let z := fun x:Site (g w)=>peakT x (μ w); have ht' (x:Site (g w)): ‖neap 3 (fern (V w) (F w) a (sip x)) 0 p‖ ≤ c*(z x)⁻¹ ^ (5:ℕ):=by
       rw[mosso h hy hs a w x p]; unfold c; rw [inv_pow, sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_); rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun j _=>hw i j x)
    have hn:0 < Wsc (g w):=inv_pos.mpr cents_pos
    rw[pond_j h hy hs a w p,norm_smul,Real.norm_of_nonneg hn.le]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun x _=>ht' x)) hn.le).trans ?_
    rw [← Finset.mul_sum,mul_left_comm]; apply (mul_le_mul_of_nonneg_left (sip_charge (f:=g w) (hx.trans (ht w).1)) hc).trans_eq; unfold a'; ring
lemma arc_y (d i b:Axis)(q:G.ColorIndex) : ∃ C:ℝ,0 ≤ C ∧ ∀ (δ:ℝ),0 < δ→ ∀ (μ:W→ℝ), (∀ w, δ ≤ μ w ∧ μ w≤1) → ∀ A' σ, 0<σ→ (∀ w,Skew (summitM (U w) (μ w)).back σ A')→ ∀ H:(∀ w,WildM G (g w) k k), (∀ w,Ticket (summitM (U w) (μ w)).back (H w))→
    ∀ᶠ w in L', ‖lux d i q b (fun x=>trace (H w x*F w x))‖ ≤ C*(μ w)⁻¹:=by
    let A(t:Dish):=lawn d b t
    choose C hC H using (fun t:Dish=> arc_r h (mood G i q) (A t) hp Q)
    let D(x:ℤ):=8*(C (x,1)+C (x,-1))+(C (x,2)+C (x,-2)); have hD(x):0 ≤ D x:=by unfold D; have hp:=hC (x,1); have hv:=hC (x,-1); have hu:=hC (x,2); have he:=hC (x,-2); positivity
    let E:=D 1+2*D 0+D (-1); have hE:0≤ E:=by unfold E; have hx:=hD 1; have he:=hD 0; have hz:=hD (-1); positivity
    refine ⟨1+E,by positivity,fun δ hd μ he A' σ hp hy Q' hh=>?_⟩
    let F'(w:W)(t:Dish):= neap 3 (Pond (F w) (mood G i q) (summitM (U w) (μ w)).back) 0 (A t)
    let B(w):= lux d i q b (fun x=>trace (Q' w x*F w x)); let X(w):= Deb (F' w)
    have hv: Rose L' B X:= plankL Q d i b q h hh hy hp
    let c:= fun w=> (μ w)⁻¹
    have hM(t:Dish): ∀ᶠ w in L', ‖F' w t‖ ≤ C t*c w:= H t δ hd μ he A' σ hp hy
    let G' w p:=FlopZ fun y=> F' w (p,y); have hy(x:ℤ): ∀ᶠ w in L', ‖G' w x‖ ≤ D x*c w:=by
       filter_upwards[hM (x,1),hM (x,-1),hM (x,2),hM (x,-2)] with w h1 h2 h3 h4
       let f(y):=F' w (x,y); rw[show G' w x= _ from flopi f,norm_mul]; refine (mul_le_of_le_one_left (norm_nonneg _) (show ‖(1/12:ℂ)‖≤1 by norm_num)).trans ((norm_sub_le ..).trans ?_)
       rw[norm_mul,show ‖(8:ℂ)‖=(8:ℝ) by norm_num]; refine (add_le_add (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add h1 h2)) (by norm_num)) ((norm_sub_le ..).trans (add_le_add h3 h4))).trans_eq ?_; unfold D;ring
    filter_upwards [hy 1,hy 0,hy (-1),hv.eventually (ball_mem_nhds 0 zero_lt_one)] with w h1 h2 h3 h4
    have hx: ‖X w‖ ≤ E*c w:=by
       rw[show X w= Complex.I*PanZ (G' w) from rfl, norm_mul,Complex.norm_I,one_mul,pani,norm_mul]; refine (mul_le_of_le_one_left (norm_nonneg _) (show ‖(1/2:ℂ)‖≤1 by norm_num)).trans ((norm_add_le ..).trans ?_)
       refine (add_le_add ((norm_sub_le ..).trans (add_le_add h1 (show ‖(2:ℂ)*G' w 0‖ ≤ 2*(D 0*c w) from ?_))) h3).trans_eq ?_
       · rw[norm_mul]; norm_num; linarith
       unfold E; ring
    have hl:‖B w-X w‖ ≤ 1:=by simpa [Metric.mem_ball, dist_eq_norm] using le_of_lt (show dist ((B-X) w) 0<1 from h4)
    have ht:1 ≤ c w:= (one_le_inv₀ (hd.trans_le (he w).1)).2 (he w).2
    rw [show lux d i q b _=B w from rfl, add_mul,one_mul,← sub_add_cancel (B w) (X w)]; exact (norm_add_le ..).trans (add_le_add (hl.trans ht) hx)
end YM.Trace.Loft

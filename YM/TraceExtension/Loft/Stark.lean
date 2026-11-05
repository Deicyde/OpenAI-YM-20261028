import YM.TraceExtension.Lamp.Pine
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{G:Gauge}{g:W→Side}{q:Clip}{k m n:ℕ}{σ A C D B ε L δ M:ℝ}
variable {F:∀ w, WildM G (g w) k k}{L':Filter W} (h:Oil L' F)(a:Fslot G)(p:Land)
variable {U:Coast k G W}(hp:Sand U)(Q:Tendsto (fun w=>(g w).val) L' atTop)
include h hp
lemma ar_lo (i j:Loc G k) :∃ A:ℝ, 0 ≤ A ∧ ∀ (δ:ℝ), 0 < δ → ∀ (μ:W→ℝ), (∀ w,δ ≤ μ w∧ μ w≤1)→ ∀ A' σ, 0<σ → (∀ w,Skew (summitM (U w) (μ w)).back σ A')→ ∀ᶠ w in L',∀ x:Site (g w),
    let z:=peakT x (μ w); let V:=moss (summitM (U w) (μ w)).back (F w) (sip x) a i j;
    ‖neap 2 V 0 p‖ ≤ A* (z^5)⁻¹:=by
    obtain ⟨C,hC,H⟩:= noting h a p i j hp
    let ℓ:ℝ:= (((Nat.factorial 2):ℝ)⁻¹*C); have hL: 0≤ℓ:= by unfold ℓ; positivity
    refine ⟨ℓ*furthest,mul_nonneg hL furthest_pos,fun δ hd μ ht A' σ hx hf=>?_⟩
    obtain ⟨D,hD,K⟩:= (honor_sq h hf hx i j a (n:=3)).top
    filter_upwards[H δ hd] with w hw x; intro z V
    have he:= (ht w).1; have hz:0 < z:= add_pos_of_nonneg_of_pos (orbit_nonneg _) (hd.trans_le he); have hh:= norm_neap (p:= (1:ℝ)) (hw x (μ w) he (ht w).2) (by decide : 2≤3)
    have ha: ContDiffAt ℝ ω V 0:= (shunt_a (sip x) 0 (K w (sip x,0))).analytic
    have hs: z^ (2:ℕ) * ‖neap 2 V 0 p‖ ≤ (((Nat.factorial 2):ℝ)⁻¹)* (C*(z^2)⁻¹):=by
       have he: neap 2 (fun t:ℝ=> V (t • z • p)) 0 1=z^ (2:ℕ) • neap 2 V 0 p:=by simp_rw[← neap_tide]; rw[← chord_n (0:Land) (z • p) 2 ha]; simp
       rw[he,norm_smul,Real.norm_of_nonneg (pow_nonneg hz.le _),norm_one, one_pow,mul_one] at hh; exact hh
    have hu: z ≤ furthest:= (add_le_add (orbit_boundary _ (sip_n x)) (ht w|>.2)).trans_eq (add_comm ..)
    apply le_trans ((le_div_iff₀ (pow_pos hz 2)).mpr ((mul_comm ..).trans_le hs)); rw[show _/z^2=ℓ*z*(z^5)⁻¹ by unfold ℓ; field_simp <;> ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hL) (by positivity)
include Q
lemma reef : ∃ A:ℝ,0 ≤ A ∧ ∀ (δ:ℝ), 0 < δ→ ∀ (μ:W→ℝ), (∀ w, δ ≤ μ w ∧ μ w≤1) → ∀ A' σ, 0<σ → (∀ w,Skew (summitM (U w) (μ w)).back σ A')→ ∀ᶠ w in L',
    ‖neap 2 (Pond (F w) a (summitM (U w) (μ w)).back) 0 p‖≤ A*(μ w)⁻¹:=by
    choose C hC H using (fun i j=>ar_lo h a p hp i j)
    let c:=∑ i, ∑ j,C i j; have hc: 0 ≤ c:=sum_nonneg fun i _=>sum_nonneg fun j _=>hC i j
    let a':ℝ:=2*6^4/(2*Real.pi)^4; have ha':0 ≤ a':=by unfold a'; positivity
    refine ⟨c*a',by positivity,fun δ hδ μ ht A' σ hs hy=>?_⟩
    let V i:= (summitM (U i) (μ i)).back
    have hh:∀ᶠ w in L',∀ i j (x:Site (g w)), ‖neap 2 (moss (V w) (F w) (sip x) a i j) 0 p‖≤ C i j * ((peakT x (μ w))^5)⁻¹ := eventually_all.mpr fun i=> eventually_all.mpr fun j=> H i j δ hδ μ ht A' σ hs hy
    filter_upwards [hh,(gran Q).void.eventually (ge_mem_nhds hδ)] with w hw hx
    let N:=Wsc (g w); let z := fun x:Site (g w)=>peakT x (μ w); have ht' (x:Site (g w)): ‖neap 2 (fern (V w) (F w) a (sip x)) 0 p‖ ≤ c*(z x)⁻¹ ^ (5:ℕ):=by
       rw[mosso h hy hs a w x p]; unfold c; rw [inv_pow, sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_); rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun j _=>hw i j x)
    have hn:0 < Wsc (g w):=inv_pos.mpr cents_pos
    rw[pond_j h hy hs a w p,norm_smul,Real.norm_of_nonneg hn.le]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun x _=>ht' x)) hn.le).trans ?_
    rw [← Finset.mul_sum,mul_left_comm]; apply (mul_le_mul_of_nonneg_left (sip_charge (f:=g w) (hx.trans (ht w).1)) hc).trans_eq; unfold a'; ring
lemma cob_hou (d i:Axis)(q:G.ColorIndex) : ∃ C:ℝ,0 ≤ C ∧ ∀ (μ:ℝ),0 < μ→ μ≤1→ ∀ A' σ, 0<σ→ (∀ w,Skew (summitM (U w) μ).back σ A')→ ∀ H:(∀ w,WildM G (g w) k k), (∀ w,Ticket (summitM (U w) μ).back (H w))→
    ∀ᶠ w in L', ‖Lamp.cob d i q (fun x=>trace (H w x*F w x))‖ ≤ C*μ⁻¹:=by
    let p:Land:=![step d,-step d]; obtain ⟨C,hC,H⟩:=reef h (mood G i q) p hp Q
    refine ⟨1+C,by positivity,fun μ hμ hm A' σ hs hy U' hu=>?_⟩; have hm'(_:W): μ ≤ μ ∧ μ ≤ 1:=⟨le_rfl,hm⟩; have ht:=H μ hμ (fun _=>μ) hm' A' σ hs hy
    let V(w):= Pond (F w) (mood G i q) (summitM (U w) μ).back; let X(w):= Lamp.cob d i q (fun x=>trace (U' w x*F w x))
    have hp'(w):Memo (F w) 0:=by obtain ⟨A,C,hA,hC,H⟩:=h.jets.top; exact fun i j=> H w i j|>.1
    have hx:Rose L' X (fun w=> neap 2 (V w) 0 p):=by
       unfold X Lamp.cob; simp_rw[clue_at d i q d, cusp d i d q (hu _) (hp' _),lawn,flee_run]; simp only [Int.cast_zero,zero_smul,add_zero];exact pan_brief (gran Q) _ p (pond_b h hy hs _)
    filter_upwards [ht,hx.eventually (ball_mem_nhds (0:ℂ) zero_lt_one)] with w hw hh; let f:=neap 2 (V w) 0 p; have hz: ‖X w-f‖<1:=by simpa only [mem_ball,dist_zero_right,Pi.sub_apply] using hh
    change ‖X w‖ ≤ _; rw [← sub_add_cancel (X w) f, add_mul,one_mul]; exact (norm_add_le ..).trans (add_le_add (hz.le.trans ((one_le_inv₀ hμ).2 hm)) hw)
end YM.Trace.Loft

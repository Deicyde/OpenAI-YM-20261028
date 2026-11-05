import YM.TraceExtension.Lamp.Jake
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{H K:WickL G}{T:Reed G}{L:Filter W}{Y:Gal G f}
-- gauge orbit about U=1
structure Tempo (F: WildM G f k k) : Prop where
    memo: Memo F 0
    sway: ∀ᶠ x:BaseSites G f in 𝓝 0, F (lull (1:Config G f) x 0)* (jerk G f k x)=jerk G f k x * F 0
lemma PaceV {p: Clip}{M:PathData G}(x:Axis)(h:Y∈ rains G f)(h':M.Bounds p α C D)(hk: (stock p M 1 (1:Config G f)).det≠0): Tempo (wB (stampQ 0) x Y ∘ input G f)∧Tempo (wG (stampQ 0) x∘ input G f):=by
    obtain ⟨hc,he⟩:= h; change Cloaked Y at hc
    have ht : Army (switchSite (G:=G) (m:=f)) 0 := Army.powG (v:=id) contDiffAt_id
    let V:= (1:Config G f); let F(p:BaseSites G f):= Lattice.gauge (switchSite p) V
    have hp:F 0=1:=by unfold F; simp [V]
    have h0: Tune Y 1:=by
       have he:= tune_n hc (input G f) (Army.powL (v:=id) contDiffAt_id) (input_zero ..); have ht: Tune Y (input G f 0):= mem_of_mem_nhds he; rwa [input_zero] at ht
    have hv : ∀ᶠ p:BaseSites G f in 𝓝 0, tidal Y (F p)*trench (switchSite p)=trench (switchSite p)*tidal Y 1:=by
        filter_upwards [tune_n hc F (ht.slant (Army.park _ _)) hp,accord_n (V:=fun _=>V) (k:=switchSite) hc (Army.park V _) rfl ht (u:=1) switch_zero] with v hv hz; exact (swapping _ _ h' zero_lt_one hk h0 hv hz).armV
    obtain ⟨hh,hH⟩:=w_memo (stampQ 0) x (V:=input G f) (hp:=input_zero ..) hc (Army.powL contDiffAt_id)
    refine ⟨⟨hh,?_⟩,⟨hH,?_⟩⟩
    all_goals filter_upwards [hv,lyric_enc V] with p hv hp; unfold V at hp; rw[mul_one] at hp; simp only[Function.comp_apply,jerk,hp,input_zero]
    · rw [quiltB]; exact (w_cross (stampQ 0) x (1:Config G f) (switchSite p) hv).1
    rw[quiltG]; exact (w_cross _ _ (1:Config G f) (switchSite p) hv).2

lemma Tempo.horn {F:WildM G f k k}(h:Tempo F)(a: Phase (Lines G f 0)): seat F (approached (mail (1:Config G f))*ᵥ a)+approached (F 0)*seat (jerk G f k) a=seat (jerk G f k) a*approached (F 0):=by
    let D:=jerk G f k; let P(x:BaseSites G f):= lull (1:Config G f) x 0;have ht:ContDiffAt ℝ ω P 0:= (lull_analytic (1:Config G f)).comp (f:=fun x:BaseSites G f=> (x,0)) _ (by fun_prop);have hP:P 0=0:=lull_o _
    have hD: Memo D 0:= memo_mailB; have hF: Memo (F ∘ P) 0:=fun i j=>ContDiffAt.comp (g:=fun x=> F x i j) 0 (hP.symm ▸ h.memo i j) ht
    let S:=approached (mail (1:Config G f));let U:=approached (F 0)
    have he(u:BaseSites G f): S *ᵥ axes u=axes (cant 1 u):= by unfold S;rw [prom_vec,mailed]
    have hu(a:BaseSites G f): directionM (F ∘ P) 0 a + F 0*directionM D 0 a=directionM D 0 a *F 0:=by
       have hh:= directions_congr (M:=fun x=> (F ∘ P) x*D x) (N:=fun x=>D x*F 0) (u:=a) h.sway
       rw [direction_prod hF hD, direction_prod hD (V:=fun _=> F 0) (Memo.raw _ _),direction_zero,show D 0=1 by unfold D jerk; rw[Function.comp_apply,switch_zero,quilt_g],one_mul,Matrix.mul_one,add_zero,Function.comp_apply,hP] at hh;exact hh
    have hx : Leads fun a=> seat F (S *ᵥ a)+U*seat D a := Leads.plus (p:=fun a=>seat F (S *ᵥ a)) (q:=fun a=> U*seat D a) ?_ ?_
    pick_goal 2
    · intro p q; dsimp only; rw[mulVec_add, mulVec_smul, he,he]; exact seat_e ..
    pick_goal 2
    · exact (seat_e D).lower U
    apply Leads.buys hx ((seat_e D).upper U) _ a
    intro x; rw [he,seating,seating]
    have hh: directionM F 0 (cant 1 x)= directionM (F ∘ P) 0 x:=by
       ext i j; let A(z):=F z i j; change fderiv ℝ A 0 _= fderiv ℝ (A ∘ P) _ _
       rw [fderiv_comp 0 (by rw[hP];exact ((h.memo i j).differentiableAt (by simp))) (ht.differentiableAt (by simp)),hP,← lull_home];rfl
    rw [hh];unfold U;rw [← prom_mul,← prom_addition,hu, prom_mul]
lemma chi_price {F:WildM G f k k}(h:Tempo F)(p:Site f)(a:G.ColorIndex) (i:Axis)(hz:∀ j:Axis, j≠i→ cell p (step j)=1):
    let D:= seat (jerk G f k) (relay p (vac,a));let U:=approached (F 0);
    (1-cell p (step i)) • seat F (relay p (coord i,a))=D*U-U*D:=by
    intro D U; have hh:= h.horn (relay p (vac,a)); rw [mail_sign,sum_eq_single i] at hh; swap; · intro b _ hb; rw [hz b hb,sub_self,zero_smul]
    swap; · simp
    have hv (p:Phase (Lines G f 1))(c:ℂ): seat F (c • p)=c • seat F p:=by ext j k; let M:=beat (fun x=>F x j k) 0 1; change M _=_*M _; exact (by
        rw [show (![c • p]:Fin 1→ _)=fun i:Fin 1=>c • p from funext (fun i=>by fin_cases i;rfl)]; have ht:= M.map_smul_univ (fun _=>c) (fun _=>p); simp only[prod_const,card_univ,Fintype.card_fin,pow_one] at ht; rw[show (![p]:Fin 1→ _)=fun _=>p from funext (fun i=>by fin_cases i;rfl)];exact ht)
    rw [hv] at hh; exact eq_sub_of_add_eq hh
end YM.Trace.Lamp

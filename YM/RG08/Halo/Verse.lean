import YM.RG08.Halo.Charge

/-! # Polynomial stencil solution used for residual T_i cert & deterministic slot
prices. Difference for gradient may eat post tickets. E_D only. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I:Type}{L:Side}{n p q d h w e l:ℕ}{B C D J σ:ℝ}{hs:0<σ}{M:Pack n (Ed G Cover)}
local notation "A"=>Loc G 1
local notation "E"=>Ed G Cover
local notation "S"=>Nd G Cover

lemma freight {X:Carrier.Lines L}{N:Kernel G.ColorIndex A}{K:Kernel A A}(o:Site L)(x:E)(hc:Yurt.Crest L X N K)(hσ:0<σ){P T:ℝ}(hP:0≤P)(hT:0≤T)(hx:Yurt.Tutor L σ T X G 0)(h:RowCost σ L N P){f:Masked G}(he:Chit G p f B):
 melt K (lift o) (Yurt.inlet f) x = melt (Ballet G L X []) (lift o) (Yurt.inlet f) x + grad (melt N (lift o) (Yurt.inlet f)) x:=by
 let V:=Yurt.inlet f
 have ht:Bearing (stance A) p 0 B V:=exhausted he le_rfl le_rfl
 have he(t:S): Summable (push N (lift o) V t):= (row_budget h hσ hP ht o t).1.of_norm
 unfold grad melt
 rw [←Summable.tsum_sub (he _) (he _),←Summable.tsum_add (f:=push _ _ _ x) (row_budget (hx [] le_rfl) hσ (by positivity) ht o x).1.of_norm ((he _).sub (he _))]
 apply tsum_congr;intro i;unfold push;rw [hc i,Flint.grad]; change (_+ (N (x.1+lift o + _,_) i-_))* _=_
 rw [add_right_comm x.1]; ring

-- F itself gauge/no-difflaw eval and Φ repr response need extra factor |ahead | ≤4. cost beam poly?
lemma tetanus (G:Gauge)(l e n h d:ℕ)(σ τ V:ℝ)(hs:0<σ)(ht:0<τ)(hV:0≤V)(hr:n≤l+e):∃ C:ℝ,0≤C ∧ ∀ (P:GrainS (Ed G Cover))(L:Side)(o:Site L){T:ℝ}{Q:ℝ}{B:ℝ}{X:Carrier.Lines L}{N:Kernel G.ColorIndex (Loc G 1)} {K:Kernel (Loc G 1) (Loc G 1)}{ψ:Fin n→Masked G}{t:Fin n→ℕ}{a:Fin n→ℝ}(f:Pearl),Calls l P→ Permit d l P→0≤B →0≤T→0≤Q→(∀ i<e,∀ k≤l+i,Sings (stance _) d hs (P i k) B)→(∀ k≤l+e,Sings (stance _) d hs (P e k) T)→
 RowCost τ L N Q →Tutor L τ V X G 0→Crest L X N K→ (∀ i,Chit G (t i) (ψ i) (a i))→(∀ i,t i≤h)→
 let Z:=fun i=>Yurt.inlet (ψ i)
 ; |sonic (P e n) f (fun i=>melt K (lift o) (Z i))-sonic (P e n) f (fun i=>melt (Ballet G L X []) (lift o) (Z i))| ≤ C*(Q+V)^n*(∏ i,a i)*B*beam d hs f:=by
 obtain ⟨D,hD,H⟩:=spark_band G l e n h σ 0 hs le_rfl zero_le_one (by linarith) hr
 let C:=D*treasure (Loc G 1) h τ^n
 have he:0≤C:=mul_nonneg hD (pow_nonneg (treasure_nn (Loc G 1) _ ht.le) _)
 refine ⟨C,he,?_⟩
 intro P L o T Q B X N K ψ t a f hp hp' hb hT hQ hE hL hN hX hK hψ hh Z
 have hu(i):=exhausted (hψ i) (hh i) (show 0 ≤ (0:ℝ) from le_rfl)
 let Y(i:Fin n):=melt (Ballet G L X []) (lift o) (Z i)
 let U(i:Fin n):=melt N (lift o) (Z i)
 let Z'(i:Fin n):= treasure (Loc G 1) h τ*(Q+V)*a i
 have hτ:= treasure_nn (Loc G 1) h ht.le
 have hℓ:(1:ℝ)≤L.val:=Nat.one_le_cast.mpr L.property
 have hy(i): Bearing (stance (Loc G 1)) h 0 (Z' i) (Y i):=by
    apply (wallet (hX [] le_rfl) ht (by positivity) (hu i) o).up
    have hz: V/(L.val:ℝ)^(([]:List Axis).length+1)≤Q+V:=by simp only [List.length_nil,zero_add,pow_one]; exact (div_le_self hV hℓ).trans (le_add_of_nonneg_left hQ)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hτ) (hψ i).live
 have hx(i): Bearing (stance G.ColorIndex) h 0 (Z' i) (U i):= (wallet hN ht hQ (hu i) o).up (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hV) hτ) (hψ i).live)
 have hh:= (H Y U Z' hy hx P d B T f hp hp' hb hT hE hL).1
 have hk(i:Fin n):melt K (lift o) (Z i)=Y i+grad (U i):=funext fun x=>Halo.freight _ x hK ht hQ hV hX hN (hψ i)
 refine (show _ ≤ D*(∏ i,Z' i)*B*beam d hs f from by simp_rw [hk];exact hh).trans_eq ?_
 unfold C Z'; rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_pow];ring
-- no orientation. POL residual forecast each L; constants depend j,j' through h admitted. Post Q,L. Use B=lower costs and χ=C*B (or 0). Standard Condition force price shares across.
lemma chapter (G:Gauge)(l e n h d j t:ℕ)(σ τ V:ℝ)(hs:0<σ)(ht:0<τ)(hV:0≤V)(hr:n≤l+e)(hj:4≤j)(hk:4≤t)(hJ:h≤j)(π:ℝ)(hπ:0<π):∃ C:ℝ,0≤C∧∀ (P:GrainS (Ed G Cover))(Y:Flight j t)(o:Site Y.L){K:Kernel (Loc G 1) (Loc G 1)}{N:Kernel G.ColorIndex (Loc G 1)}{T Q B D:ℝ}{w:ℕ},
 let A':=Carrier.linesOf Y π
 let u:=unitStep Y.L
 ; Calls l P →Permit d l P → Tuned G n h d w σ hs (P e n) D →0≤T→0≤Q→0≤B→(∀ i<e,∀ k≤l+i,Sings (stance _) d hs (P i k) B)→(∀ k≤l+e,Sings (stance _) d hs (P e k) T)→RowCost τ Y.L N Q→ RowCost τ Y.L K Q→Tutor Y.L τ V A' G 0→Crest Y.L A' N K→∀ {ψ:Fin n→Masked G}{b:Fin n→ℕ}{a:Fin n→ℝ}(q:ℕ)(f:Cargo q),(q+∑ i,b i) ≤ h→(∀ i,1≤b i)→(∀ i,Chit G (b i) (ψ i) (a i))→
 let U:=Yurt.ferry K (P e n) u (ahead Y.L o) (Lattice.lift o); let R:= sonic U (pal f) (Yurt.inlet ∘ ψ)
 ; |R| ≤ C*((Q+V)^n*B + D*u^w)*(∏ i,a i) ∧ ((q+∑ i,b i)≤ w→ B=0 → R=u^(q+∑ i,b i)*sonic (P e n) (pal f) (Yurt.inlet ∘ ψ)):=by
 obtain ⟨c,hc,H⟩:=pay_roll G h n
 obtain ⟨b',hb',hQ'⟩:=tetanus G l e n h d σ τ V hs ht hV hr
 choose W hW Z using (fun i (hi:i≤j)=>jewels G hj hk π hπ i hi)
 let D(i:Fin (h+1)):= W i.val (by omega)
 let T':=∑ i:Fin (h+1),D i
 have hd(i:Fin (h+1)):0≤D i:= hW ..
 have hD(i:Fin (h+1)):D i≤T':= single_le_sum (f:=D) (fun i _=>hd i) (mem_univ _)
 have hT:0≤T':=sum_nonneg fun i _=>hd i
 let C₁:=c*T'^n*(5:ℝ)^h
 let H':ℝ:= (∑ i:Fin (h+1),∑ j:Cargo i.val, beam d hs (pal j))*Real.exp (σ*4)
 have hc0(s:Jetty.Jet h):beam d hs (pal s.2)*Real.exp (σ*4)≤ H':=by
    unfold H';gcongr; exact (single_le_sum (s:=univ) (f:=fun j:Cargo s.1.val=>beam d hs (pal j)) (fun i _=>beam_nn ..) (mem_univ _)).trans (single_le_sum (f:=fun i:Fin (h+1)=>∑ j:Cargo i.val,beam d hs (pal j)) (fun i _=>sum_nonneg fun _ _=>beam_nn ..) (mem_univ _))
 have hf:0≤H':=mul_nonneg (sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>beam_nn ..))) (Real.exp_pos _).le
 let C:=b'*H'+C₁
 refine ⟨C,by unfold C C₁;positivity,?_⟩;intro P Y o K N T Q B M w A' u he1 he2 he3 ht1 ht2 ht3 he4 he5 he6 he7 he8 he9 ψ b a q f hχ hχ' hg U R
 have hz(i):b i≤h:=(single_le_sum (f:=b) (s:=univ) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans (by omega)
 have hu:0<u:=unitStep_pos _;have hi:u≤1:=unitStep_le _
 choose φ Hφ hp using fun i=>Z (b i) ((hz i).trans hJ) Y o (hg i)
 let g:=aisle u (ahead Y.L o) (pal f)
 have hv : R= sonic (P e n) g (fun i=>melt K (Lattice.lift o) (Yurt.inlet (ψ i))):= melt_read he7 ht ht2 (V:=Yurt.inlet ∘ ψ) (fun i=>exhausted (hg i) (hz i) le_rfl) he3.coherent hs (he5 _ hr) ht1 o _ u _
 have hY:|R-sonic (P e n) g (Yurt.inlet ∘ φ)|≤b'*(Q+V)^n*(∏ i,a i)*B*H':=by
    rw [hv]; have h':=hQ' P Y.L o g he1 he2 ht3 ht1 ht2 he4 he5 he6 he8 he9 hg hz
    change |sonic _ g (fun i=>melt K _ (Yurt.inlet (ψ i)))-sonic _ g (fun i=>melt (Ballet G Y.L (Carrier.linesOf Y π) []) _ (Yurt.inlet (ψ i)))|≤_ at h'; simp_rw [hp] at h'
    have hs': |u|=u:=abs_of_pos hu
    refine h'.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · apply (spending (d:=d) (h:=hs) hs _ u (by rwa [hs']) (by rw [hs'];nlinarith) (pal f)).trans
      refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (heading Y.L o) hs.le)) (beam_nn ..)).trans (hc0 ⟨⟨q,by omega⟩,f⟩)
    have hy:0≤∏ i,a i:=prod_nonneg fun i _=>(hg i).live
    positivity
 obtain ⟨hr',hr''⟩:=pal_pull f u (ahead Y.L o) hu.le hi (heading Y.L o)
 have hg'(i): Pool u (b i) 1 (φ i) (T'*a i):= (Hφ i).close.up hu.le (mul_le_mul_of_nonneg_right (hD ⟨b i,by have:=hz i;omega⟩) (hg i).live) le_rfl
 have hM:=H hs he3 _ g q hu hi hχ hg' hr'
 have ha:0≤∏ i,a i:=prod_nonneg fun i _=>(hg i).live
 have htM:0≤M*u^w:=mul_nonneg he3.nonneg (pow_nonneg hu.le _)
 constructor
 · have he: |R| ≤ |R-sonic (P e n) g (Yurt.inlet ∘ φ)|+|sonic (P e n) g (Yurt.inlet ∘ φ)|:=by
      let x:=sonic (P e n) g (Yurt.inlet ∘ φ)
      conv_lhs=>rw [←sub_add_cancel R x]
      exact abs_add_le _ _
   apply he.trans ((add_le_add hY hM).trans ?_); rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
   have hC :c*T'^n* (5:ℝ)^q ≤ C := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega:q≤h)) (by positivity)).trans (le_add_of_nonneg_left (mul_nonneg hb' hf))
   nlinarith only [mul_le_mul_of_nonneg_right hC (mul_nonneg ha htM),mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (show 0≤C₁ by unfold C₁;positivity):b'*H'≤C) (show 0≤ (Q+V)^n*B*(∏ i:Fin n,a i) by positivity)] -- rewrite
 intro hq hb
 rw [hb,mul_zero,zero_mul] at hY; rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hY (abs_nonneg _)))]
 apply Halo.badges he3 hq hχ' (fun i=>(hg i).fit) (fun i=>(Hφ i).principal) (pal f) g (Place.exact_le_band (Nat.lt_succ_self _) (pal_true f)) hr''
end YM.RG08.Halo

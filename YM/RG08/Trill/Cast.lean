import YM.RG08.Flint.Hero
import YM.Next.WARD_BIN.Degree
/-! # Constant color, meter extraction. Exact all orders from Called provider.
 All finite orders independent, not connected-group restricted. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}
local notation "E"=>Ed G Cover
local notation "N"=>Nd G Cover
lemma cast_hot (d:G.El)(i:E)(X:E→ℝ)(n:ℕ) : tap (n+1) (gain d (kiosk X) (kiosk (0:N→ℝ)) i)=0:=by
 rw [tip X 0 d]
 let v:Cellar (foil G):= Flint.drift X (0:N→ℝ) ∘ jab (Quarry.hot d) i
 let f:= (Quarry.hot d).fare i.2
 let m:=n+1+1
 have hv:fbar (1:Fin 3) v=(0:G.Color):=by ext j; change v (1,j)=(0:ℝ);unfold v Flint.drift jab Function.comp Quarry.hot Quarry.menu; dsimp only; split_ifs <;> simp_all
 have hz:fbar (2:Fin 3) v=(0:G.Color):=by ext j; change v (2,j)=(0:ℝ);unfold v Flint.drift jab Function.comp Quarry.hot Quarry.menu; dsimp only; split_ifs <;> simp_all
 let w:= Quarry.fbar (0:Fin 3) v
 have ht:Tendsto (fun t:ℝ=>t • w) (𝓝 0) (𝓝 0):=by have h:Tendsto (fun t:ℝ=>t • w) (𝓝 0) (𝓝 ((0:ℝ) • w)):= continuousAt_id.smul continuousAt_const;rwa [zero_smul] at h
 have he:(fun t:ℝ=>f (t • v)) =ᶠ[𝓝 0] fun t=>t^1 • ((G.adjoint d w) i.2.2):=by
    filter_upwards [ht.eventually G.plog_left] with t h
    change G.adjoint d (G.plog (G.mat (gaugeIn 1 (fbar (0:Fin 3) (t • v)) (fbar 1 (t • v)) (fbar 2 (t • v))))) i.2.2=_
    rw [map_smul,map_smul,map_smul,hv,hz,smul_zero, gaugeIn,neg_zero,G.mat_lieExp_zero,one_mul,mul_one,one_mul,inv_one,mul_one,h,map_smul,pow_one]; rfl
 have H: MvPolynomial.eval v (Camera.print m f) = YM.WardBin.leading m (fun t : ℝ => f (t • v)):=by
    rw [←Camera.flute,Camera.glimpses ((hot d).fit _),YM.WardBin.leading_tensor v f (((hot d).fit i.2).of_le (mod_cast le_top))];rfl
 change MvPolynomial.eval v (Camera.print m f)=0; rw [H]
 have hh:YM.WardBin.leading m (fun t : ℝ => f (t • v))=YM.WardBin.leading m (fun t=>t^1 • ((G.adjoint d w) i.2.2)):=by unfold YM.WardBin.leading;rw [he.iteratedDeriv_eq]
 rw [hh,YM.WardBin.lead_monomial,if_neg (show m≠1 by unfold m;omega)]

lemma cast_series (d:G.El)(X:E→ℝ) : gain d (kiosk X) (kiosk (0:N→ℝ))=kiosk (settle d X):=by
 funext i;ext n:1
 cases n with
 | zero=>change tap 0 _=tap 0 _;rw [incoming];unfold kiosk tap;rw [PowerSeries.coeff_C,if_pos rfl,show grad (0:N→ℝ)=0 from by funext i;simp [grad],add_zero]
 | succ n=>change tap (n+1) _=tap (n+1) _;rw [cast_hot];unfold kiosk tap;rw [PowerSeries.coeff_C,if_neg (by omega)]

def lull (G:Gauge)(w:G.El) : (G.ColorIndex→ℝ) →L[ℝ](G.ColorIndex→ℝ):=(heavy G).symm.toContinuousLinearMap.comp ((G.adjoint w).toContinuousLinearMap.comp (heavy G).toContinuousLinearMap)
lemma drowse {p:ℕ}{δ a:ℝ}(w:G.El){X:E→ℝ}(he:Bearing (stance (Loc G 1)) p δ a X):Bearing (stance _) p δ (‖lull G w‖*a) (settle w X):=by
 refine ⟨mul_nonneg (norm_nonneg _) he.1,fun i=>?_⟩
 let v(j:G.ColorIndex):=X (i.1,i.2.1,j)
 change ‖lull G w v i.2.2‖≤ _ -- defeq abs?
 apply (norm_le_pi_norm _ _).trans ((lull G w).le_opNorm _|>.trans ?_)
 rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 exact (pi_norm_le_iff_of_nonneg (mul_nonneg he.1 (hustle_nn _ _ (abroad_nn i)))).mpr fun j=>he.2 (i.1,i.2.1,j)
lemma lull_sum (w:G.El){k:ℕ}(X:Fin k→E→ℝ)(u:Fin k→ℝ):settle w (∑ i: Fin k,u i • X i)=∑ i:Fin k,u i • settle w (X i):=by
 funext i
 let v(j:Fin k)(t:G.ColorIndex):=X j (i.1,i.2.1,t)
 rw [Finset.sum_apply];change lull G w (fun t=>(∑ j:Fin k,u j • X j) (i.1,i.2.1,t)) i.2.2= ∑ j:Fin k,u j • lull G w (v j) i.2.2
 rw [show (fun (t:G.ColorIndex)=>(∑ j:Fin k,u j • X j) (i.1,i.2.1,t))=∑ j:Fin k,u j • v j from funext (fun t=>by simp [v]),map_sum];simp

-- Use simultaneous pitches and cutoff all degrees with individual available widths.
lemma housed {l e n d:ℕ}{P:GrainS E}(hc:Calls l P)(hp:Permit d l P)(hn:n≤l+e)(w:G.El)(f:Pearl){p:ℕ}(a:Fin n→ℝ)(X:Fin n→E→ℝ)
 (hs:∀ i,Bearing (stance _) p 0 (a i) (X i))(hf:∀ i,Fenced (X i)) : sonic (P e n) f (fun i=>settle w (X i))=sonic (P e n) f X:=by
 let Y(i:Fin n):=settle w (X i)
 let F(k:ℕ):Flake k (Fin n):=modal (P e k) f Y-modal (P e k) f X
 have ha(k):Lyrics (P e k):=(hp.price e k).1
 have hY(i):Bearing (stance _) p 0 (‖lull G w‖*a i) (Y i):=drowse w (hs i)
 obtain ⟨C,_,H⟩:=septet (fun _=>0) hn (id:Fin n→Fin n)
 have hb(k):Forms.Sym (F k):=fun s=>funext fun i=> congrArg₂ (fun x y:ℝ=>x-y) (congrFun (modal_sym (X:=Y) f (hp.fine f e k) s) i) (congrFun (modal_sym (X:=X) f (hp.fine f e k) s) i)
 refine sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ?_ (abs_nonneg _)))
 change |F n id|≤0;apply (H (0:ℝ) F le_rfl (fun i _=>hb i) ?_).trans; simp
 intro u;let V:E→ℝ:=∑ i:Fin n,u i • X i
 have hA:=ward_range (M:=P) (e:=e) hc w (X:=V) (Fenced.sum _ _ (fun i _=> (hf i).smul _)) (U:=0) Fenced.zero f
 simp_rw [cast_series] at hA
 rw [sum_eq_zero (fun k hk=>sum_eq_zero (fun i (_:i∈range (l+k+1))=>bond_drop f (settle w V) (P k i) (show e-k≠0 from by simp only [mem_range] at hk;omega)))] at hA
 refine le_of_eq ?_
 rw [mul_zero,abs_eq_zero]
 rw [←neg_zero,←hA,neg_sub,←sum_sub_distrib]
 apply sum_congr rfl;intro k _
 obtain ⟨σ,hσ,T,hT⟩:=(hp.price e k).2
 -- T may <0. monotone
 rw [leanTag,show grad (0:N→ℝ)=0 from by funext i;simp [grad],add_zero,lull_sum]
 rw [modal_read (n:=k) f (ha k) hT.2 hT.1 u _ (le_rfl: (0:ℝ)≤0) (by rw [mul_zero]; linarith) hY,modal_read f (ha k) hT.2 hT.1 u _ (le_rfl:(0:ℝ)≤0) (by rw [mul_zero]; linarith) hs,parley_street,parley_street,←sum_sub_distrib]
 apply sum_congr rfl;intro _ _; exact sub_mul ..
/-- Exact symmetry on polynomial-growth coefficients. Test horizon d derivative. -/
theorem holy {l e n d:ℕ}{P:GrainS E}(hc:Calls l P)(hp:Permit d l P)(w:G.El)(f:Pearl){p:ℕ}(a:Fin n→ℝ)(X:Fin n→E→ℝ)
 (hs:∀ i,Bearing (stance _) p 0 (a i) (X i)) : sonic (P e n) f (fun i=>settle w (X i))=sonic (P e n) f X:=by
 by_cases hn:P e n=0; · rw [hn]; apply tsum_congr; intro i; simp [tote]
 let Y(s:Finset Cover)(i:Fin n):E→ℝ:=fun j=> if j.1∈s then X i j else 0
 have H(s i):Bearing (stance _) p 0 (a i) (Y s i):=⟨(hs i).1,fun j=>by unfold Y; split; exact (hs i).2 j; rw [abs_zero]; exact mul_nonneg ((hs i).1) (hustle_nn _ _ (abroad_nn j))⟩
 have h(s i):Fenced (Y s i):=⟨s×ˢ univ,fun j hj=> if_neg (by simpa using hj)⟩
 have hx(s):=housed hc hp (hp.lit e n hn) w f a (Y s) (H s) (h s)
 obtain ⟨σ,hσ,T,hT,h'E⟩:=(hp.price e n).2
 have hu(i j):Tendsto (fun s=>Y s i j) atTop (𝓝 (X i j)):= Filter.EventuallyEq.tendsto (by filter_upwards [eventually_ge_atTop ({j.1}:Finset Cover)] with t ht; exact if_pos (ht (mem_singleton.mpr rfl)))
 have ht(i j): Tendsto (fun s=>settle w (Y s i) j) atTop (𝓝 (settle w (X i) j)):=by
    change Tendsto (fun s=> lull G w (fun c=>Y s i (j.1,j.2.1,c)) j.2.2) _ _
    exact (((continuous_apply _).tendsto _).comp ((lull G w).continuous.tendsto _)).comp (tendsto_pi_nhds.mpr fun _=>hu ..)
 have hy:(n:ℝ)*0≤σ/2:=by rw [mul_zero];exact (half_pos hσ).le
 have hv:=sonic_turn f (hp.price e n).1 h'E hT hu (le_rfl:(0:ℝ)≤0) hy H
 have hz:=sonic_turn f (hp.price e n).1 h'E hT (X:=fun s i=>settle w (Y s i)) ht (le_rfl:(0:ℝ)≤0) hy (a:=fun i=>‖lull G w‖*a i) (fun s i=>drowse _ (H s i))
 exact tendsto_nhds_unique_of_eventuallyEq hz hv (.of_forall hx)
end YM.RG08.Trill

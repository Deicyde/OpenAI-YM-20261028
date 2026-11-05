import YM.RG08.Halo.Screen
/-! # Polynomial rows reissued. Chit budget, graded. principal-alias convention on
standard polynomial directions PER offset. Displacement degrades only strictly.
Preserves pre-L smoothing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I J:Type}{i n m k p d:ℕ}{u D C B θ σ:ℝ}{L:Side}{K:Kernel I J}
local notation "A"=>Loc G 1

-- `Polynomial normalization` ticket. includes expanded ranks & P-quads projection.
structure Diamond (u:ℝ)(f g:Masked G)(n:ℕ)(D:ℝ):Prop where
 close : Pool u n 1 g D
 principal : g-u^n • f ∈ Place.rangeLt (Loc G 1→ℝ) (n-1)
-- Opens even at L term. demand n ≤ j. f relation natural center f(0) input e3 vs...
lemma jewel (G:Gauge){j t:ℕ}(hj:4≤j)(ht:4≤t){k:ℝ}(hk:0<k)(n:ℕ)(hn:n≤j):∃ C':ℝ, 0≤C' ∧ ∀ (P:Flight j t){f:Masked G}{D:ℝ}(o:Site P.L),Chit G n f D → ∃g:Masked G,Diamond (Carrier.unitStep P.L) f g n (C'*D) ∧ ∀ v:Cover,relay G g (Place.seat v)=Carrier.applyLine (Carrier.linesOf P k) (Carrier.verdict (relay G f)) (v+lift o):=by
 let K:=Axis→G.Color
 let a:=‖(bonnet G).toContinuousLinearMap‖; let b:= ‖(bonnet G).symm.toContinuousLinearMap‖
 obtain ⟨W,hW,H⟩:= Carrier.deliver (E:=G.Color) _ hk hj ht n hn
 obtain ⟨U,hU,F⟩:= disclose K n
 let C':= b*(5^n:ℝ)*(n:ℝ)*W*n*(U*a)
 have ha:0≤a:=norm_nonneg _; have hb:0≤b:=norm_nonneg _
 refine ⟨C',by unfold C';positivity,fun P f D o hx=>?_⟩
 let u:=unitStep P.L;let y:=relay G f
 have hp:Pool 1 n 1 y (a*D):= Pool.stir (bonnet G).toContinuousLinearMap (Halo.Chit.at hx)
 obtain ⟨q,hq,hqr⟩:=Halo.reading y hp.band
 have hz(i:Fin n):‖q i‖≤U*(a*D):=by
    have h:=F q hq (u:=1) (m:=1) (D:=a*D) (hqr.symm ▸ hp) (by norm_num) i; simpa only [one_pow,mul_one] using h
 obtain ⟨r,H⟩:= H P q
 have hα:Carrier.charted q=y:=hqr
 let s:=Carrier.charted r;let v:=Place.seat (lift o);let t(x:E4):=s (x+v)
 refine ⟨depict G t,?_,fun i=>?_⟩;swap
 · rw [relay_back,←show y=relay G f from rfl,hα.symm,H.rolled];unfold Carrier.verdict t v; rw [Place.seat_add] 
 have hu:=unitStep_pos P.L;have hf:=hx.live
 let p:ℝ:= n*W*n*(U*a)*D
 have hp':0≤p:=by unfold p; positivity
 have hR:Pool u n 1 s p:=by
    refine ⟨Carrier.read_poly _,hp',fun x=>?_⟩
    let Z:ℝ:=W*n*(U*a)*D
    let c:= 1+u*‖x‖; have hc:1≤c:=le_add_of_nonneg_right (mul_nonneg hu.le (norm_nonneg _))
    unfold s Carrier.charted;rw [Finset.sum_apply]
    apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>Z*u*c^n) (fun i _=>?_)).trans_eq ?_)
    swap
    · have ht:‖Tensor.diagonal (r i) x‖≤‖r i‖*‖x‖^i.val:=by simpa only [Tensor.diagonal,prod_const,card_univ,Fintype.card_fin] using (r i).le_opNorm (fun _=>x)
      apply ht.trans
      have hv:pile q ≤ n*(U*(a*D)):= (sum_le_sum (fun j (_:j∈univ)=>hz j)).trans_eq (by rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul])
      have hZ: ‖r i‖ ≤ Z*u^(i.val+1):= (H.pay i).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by linarith only [hW])) (pow_nonneg hu.le _)).trans_eq (by unfold Z u;ring))
      have he : (u*‖x‖)^i.val ≤ c^n:= (pow_le_pow_left₀ (mul_nonneg hu.le (norm_nonneg _)) (le_add_of_nonneg_left zero_le_one) i.val).trans (pow_le_pow_right₀ hc i.isLt.le)
      exact (mul_le_mul_of_nonneg_right hZ (pow_nonneg (norm_nonneg _) _)).trans ((mul_le_mul_of_nonneg_left he (show 0≤Z*u by unfold Z; have hu:0 < u:=unitStep_pos _;positivity)).trans' (le_of_eq (by rw [mul_pow];ring)))
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];unfold p c Z;ring
 have hc:u*‖v‖≤4:=by
    have he:=heading P.L o;rw [ahead,norm_smul] at he;change ‖u‖*‖Place.seat (lift o)‖ ≤ 4 at he;rw [Real.norm_of_nonneg hu.le] at he;exact he
 obtain ⟨h₁,h₂⟩:= hR.turn hu.le hc
 have hP :C'*D=b*(p*(1+4)^n):=by unfold C' p;norm_num; ring
 constructor
 · rw [hP]; exact Pool.stir (bonnet G).symm.toContinuousLinearMap h₁
 let Q:=Place.rangeLt K (n-1)
 rw [← depict_back f,← depict_smul,← depict_sub]
 apply Place.linear_band (bonnet G).symm.toContinuousLinearMap (f:= t-u^n • relay G f) _
 change t-u^n • y∈Q
 have hd:t-s∈Q:=h₂
 rw [show t-u^n • y=t-s+(s-u^n • y) by abel];exact Submodule.add_mem _ hd (hα ▸ H.sameTop)

variable {j t:ℕ}{W:Flight j t}
lemma jewels (G:Gauge)(hj:4≤j)(ht:4≤t)(k:ℝ)(hk:0<k)(n:ℕ)(hn:n≤j):∃ C':ℝ,0≤C'∧ ∀ (W:Flight j t)(o:Site W.L){V:Masked G}{D:ℝ},Chit G n V D→∃ f:Masked G,
 Diamond (unitStep W.L) V f n (C'*D) ∧ melt (Ballet G W.L (Carrier.linesOf W k) []) (lift o) (Yurt.inlet V)=Yurt.inlet f:=by
 obtain ⟨C,hC,H⟩:=jewel G hj ht hk n hn
 obtain ⟨σ,U,hσ,hU,h⟩:= Carrier.priced k hk hj ht;let D':= Real.exp (4*σ)*U
 have hP:0≤D':=by unfold D';positivity
 refine ⟨C,hC,fun W o V D ht'=>?_⟩
 obtain ⟨f,hW,hw⟩:=H W o ht'
 let M:=Carrier.linesOf W k
 have he:Tutor W.L σ D' M G 0:=fun w hw=> Aura.coloring (RowCost.mono (θ:=σ) (p:=D'/(W.L.val:ℝ)^(w.length+1)) (by simpa only [D',M,mul_div_assoc,Nat.add_comm 1] using! (cross_row (h W w (by omega)) hσ.le le_rfl)) le_rfl)
 refine ⟨f,hW,?_⟩;funext x;rw [ballet_read (Carrier.stored W k hk ht) V ht' he hσ hP o x,←hw]; change f (Place.seat x.1) (coord (back x.2.1),x.2.2)=_;rw [show coord (back x.2.1)=x.2.1 from axisEquiv.apply_symm_apply _];rfl
end YM.RG08.Halo

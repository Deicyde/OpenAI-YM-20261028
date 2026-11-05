import YM.RG08.Halo.Verse

/-!
# Root-transmitted joint jet, calibrated. Captures strict triangular
pre-factor unconditioned and supplies lower price for arbitrarily many
positive coeff ages. All χ shared using Props supply.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I:Type}{L:Side}{n p q d h w e l:ℕ}{B C D J σ:ℝ}{hs:0<σ}{M:Pack n (Ed G Cover)}
local notation "A"=>Loc G 1
local notation "E"=>Ed G Cover

lemma sonicF [Fintype I](P:I→Pack n E)(f:Pearl)(a:ℝ){V:Fin n→Masked G}{b:Fin n→ℕ}(he:∀ i,∃ (d:ℕ)(σ:ℝ)(h:0<σ)(C:ℝ),Lyrics (P i)∧0≤C∧Sings (stance A) d h (P i) C)
 (hv:∀ i,V i∈Place.rangeLt _ (b i)): sonic (a •∑ i,P i) f (Yurt.inlet ∘ V)=a*∑ i,sonic (P i) f (Yurt.inlet ∘ V):=by
 choose D hD using fun i=>chitQual (hv i)
 let s:=∑ i,b i; have hc(i): Bearing (stance A) s 0 (D i) (Yurt.inlet (V i)):=exhausted (hD i) (single_le_sum (f:=b) (fun i (_:i∈(univ: Finset (Fin n)))=> Nat.zero_le _) (mem_univ _)) le_rfl
 have hX(i):Summable fun x:Tape n E=>P i x f*flakes (Yurt.inlet ∘ V) x:=by
    obtain ⟨D,σ,h,C,h₁,h₂,h₃⟩:=he i;exact (sonic_abs h₁ h₃ h₂ _ le_rfl (by linarith) hc).of_norm
 unfold sonic tote; simp_rw [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,mul_assoc a,sum_mul,tsum_mul_left];congr 1; rw [Summable.tsum_finsetSum (f:=fun i x=>P i x f*_ ) (fun i _=>hX i)]

-- full output arbitrary test still at unbounded. t barrier includes λ. Powers Lebesgue threshold.
lemma ferry_lives {K:Kernel A A}(P:Pack n E){C s B:ℝ}(he:RowCost s L K C)(ht:0<C)(h0:0< s)(hσ:0<σ)(hs:Sings (stance A) d hσ P B)(hb:0≤B)(hh:Lyrics P)(o:Site L):
 let F:=Yurt.ferry K P (unitStep L) (ahead L o) (lift o)
 ; Lyrics F ∧∃ (τ:ℝ)(hτ:0<τ)(C:ℝ),0≤C ∧ Sings (stance A) d hτ F C:=by
 intro F
 -- choose τ tiny s etc, price using tender & star
 let t:=min σ (s/(4:ℝ)); let τ:= t/(((n:ℝ)+1)*8)
 have hg:0<t:=lt_min hσ (by positivity); have hτ:0<τ:=by unfold τ;positivity
 have hm: (2*τ)/(L.val:ℝ)≤ 2*τ:=div_le_self (by positivity) (Nat.one_le_cast.mpr L.property)
 have hn : (n:ℝ)*(2*τ)≤σ/2:=by
    have hn:(n:ℝ)*(2*τ)≤( (n:ℝ)+1)*(2*τ):=by gcongr; simp
    calc
     _ ≤ _ := hn
     _ = t/4:=by
       unfold τ;have hp:(0:ℝ)<(n:ℝ)+1:=by positivity
       field_simp;ring
     _ ≤ _:=by have he:t≤σ:=min_le_left ..;linarith
 have hv:τ≤t:=by unfold τ;exact div_le_self hg.le (by linarith [Nat.cast_nonneg (α:=ℝ) n])
 have hz:2*τ≤ s:=by linarith only [hv,min_le_right σ (s/(4:ℝ)),h0]
 let a(y:ℝ)(x:Tape n E)(i:Fin n):=tender K (lift o) y (x i)
 let D₀:=C*Real.exp (4*s)
 have hp(y i):Bearing (stance A) 0 (2*τ) D₀ (a (2*τ) y i):=tender_bearing (by positivity) hz he ht.le hm o _
 have hp₀(y i): Bearing (stance A) 0 (2*τ) D₀ (a 0 y i):=tender_bearing le_rfl h0.le he ht.le (by simp;positivity) o _
 let R:=Flint.tribute (n:=n) 0 σ (fun _=>D₀)*B*Real.exp (4*τ);have hR:0≤R:=by unfold R; have hv:= Flint.tribute_nn (a:=fun _:Fin n=>D₀) σ hσ.le (fun _=>by unfold D₀;positivity) 0; positivity
 let u:=unitStep L; have hi:0<u:=unitStep_pos _; have hx:u≤1:=unitStep_le _;let v:=ahead L o
 refine ⟨fun i=>voiced ((Yurt.star (X:=a 0 i) hh hs hb (show 0 ≤ 2*τ by positivity) hn (hp₀ i)).comp (Lagoon.aisle u v)),τ,hτ,R*rate (Loc G 1) τ ^ n,by positivity [rate_nn (Loc G 1) τ],Yurt.have_sings F hτ hR ?_⟩ -- hτ weird, replace
 intro f x;change |(∏ i,Yurt.load (2*τ) (x i)) * Yurt.ferry _ _ _ _ _ x f| ≤ _
 rw [←ferry_spin]; apply (sonic_le hh hs hb (aisle u v f) (show 0≤2*τ by positivity) hn (hp x)).trans
 have he:= spending (d:=d) (h:=hσ) hτ v u (by rw [abs_of_pos hi];exact hx) (by rw [abs_of_pos hi]; exact (mul_le_of_le_one_right hτ.le hx).trans (hv.trans (min_le_left ..))) f
 apply le_trans (mul_le_mul_of_nonneg_left he (mul_nonneg (Flint.tribute_nn σ hσ.le (fun (_:Fin n)=>by unfold D₀;positivity) 0) hb))
 have ht':τ*‖v‖ ≤ 4*τ:=by have hv:=heading L o;nlinarith
 unfold R; rw [mul_comm (beam _ _ f),←mul_assoc];have hv:= Flint.tribute_nn (a:=fun _:Fin n=>D₀) σ hσ.le (fun _=>by unfold D₀;positivity) 0;have hF:=beam_nn d hτ f;gcongr -- manipulate

/-- engineered polynomial diagonal before whole graph recursion. Rank positive-order output
 Minored <= fixed lower + input T *L^{h-w}, use w=0 for unmatched, T jac canned.
- B is lower-order tickets, D controls input evaluations. Exact principal propagation only at
 B=0 (and hence e=0 or δ differences grade). Rigorous statement used for limiting readout. -/
theorem baton (G:Gauge)(l e n h d j t:ℕ)(σ τ V:ℝ)(hs:0<σ)(ht:0<τ)(hV:0≤V)(hr:n≤l+e)(hj:4≤j)(hk:4≤t)(hJ:h≤j):∀ (K:KernelChoices),∃ C:ℝ,0≤C ∧ ∀ (P:GrainS (Ed G Cover))(Y:Flight j t)(L:Patch)(b':Bed){N:Kernel G.ColorIndex (Loc G 1)}{T Q B D:ℝ}{w:ℕ}(hA:L.L=Y.L),
 let π:=K.penalty; let W (P:Side)(h:P=Y.L):Carrier.Lines P:= (h.symm ▸ Carrier.linesOf Y π);let U:=L.L; let X:= Cell.plotted L K G b';let _u:=unitStep U
 ; Calls l P →Permit d l P → Tuned G n h d w σ hs (P e n) D →w≤h→0≤T→0≤Q→0≤B→(∀ i<e,∀ k≤l+i,Sings (stance _) d hs (P i k) B)→(∀ k≤l+e,Sings (stance _) d hs (P e k) T)→RowCost τ U N Q→ RowCost τ U X Q→Tutor U τ V (W U hA) G 0→Crest U (W U hA) N X→∀ {ψ:Fin n→Masked G}{b:Fin n→ℕ}{a:Fin n→ℝ}(q:ℕ)(f:Cargo q),(q+∑ i,b i) ≤ h→(∀ i,1≤b i)→(∀ i,Chit G (b i) (ψ i) (a i))→
 let F:=Yurt.forecast L K b' P h; let S(T:GrainS (Ed G Cover)):= sonic (T e n) (pal f) (Yurt.inlet ∘ ψ)
 ; |S F| ≤ C*(((Q+V)^n*B)*(L.L.val:ℝ)^h + D*(L.L.val:ℝ)^(h-w))*(∏ i,a i) ∧ ((q+∑ i,b i)≤ w→ B=0 → S F=(L.L.val:ℝ)^(h-(q+∑ i,b i))*S P):=by
 intro K
 obtain ⟨C,hC,H⟩:= chapter G l e n h d j t σ τ V hs ht hV hr hj hk hJ K.penalty K.penalty_pos
 refine ⟨C,hC,?_⟩; intro P Y L b' N T Q B D w H' π W U X u hP hP' hp hw hT hQ hB hV' hX hN hK hτ hK' ψ b a q f hb hv hψ F S
 have HE(o:Site U):
    let TA:=Yurt.ferry X (P e n) u (ahead U o) (lift o); let R:= sonic TA (pal f) (Yurt.inlet ∘ ψ)
    ; |R|≤ C*((Q+V)^n*B+D*u^w)*(∏ i,a i) ∧ ((q+∑ i,b i)≤ w→ B=0→ R=u^(q+∑ i,b i)*S P):=by
    have h(z:Side)(h:z=Y.L)(o:Site z)(N:Kernel G.ColorIndex (Loc G 1))(X:Kernel (Loc G 1) (Loc G 1)):
      RowCost τ z N Q → RowCost τ z X Q → Tutor z τ V (W z h) G 0 →Crest z (W z h) N X→
      let u':=unitStep z;let TA:=Yurt.ferry X (P e n) u' (ahead z o) (lift o); let R:=sonic TA (pal f) (Yurt.inlet ∘ ψ)
      ; |R| ≤ C*((Q+V)^n*B+D*u'^w)*(∏ i,a i)∧ ( q+∑ i,b i≤w→B=0→R=u'^(q+∑ i,b i)*S P):=by
      subst z
      exact fun he hf hh hj=>H P Y o hP hP' hp hT hQ hB hV' hX he hf hh hj q f hb hv hψ
    exact h U H' o N X hN hK hτ hK'
 let α:=Site U
 let a':ℝ:= U.val;have ha:0<a':=by unfold a';positivity
 let c:ℝ:=Fintype.card α;have hc:0<c:=Nat.cast_pos.mpr Fintype.card_pos
 let G'(i:α):Pack n (Ed G Cover):=Yurt.ferry X (P e n) u (ahead U i) (lift i)
 let G''(i:α):=sonic (G' i) (pal f) (Yurt.inlet ∘ ψ)
 let TA:ℝ:= a'^h /c;have hAA:0≤TA:=by unfold TA; positivity
 let Y':ℝ:=C*((Q+V)^n*B+D*u^w)*(∏ i,a i)
 have hv': F e n =TA • ∑ i,G' i:=by unfold F Yurt.forecast;rw [Pi.smul_apply, Pi.smul_apply, Finset.sum_apply,Finset.sum_apply]; unfold G' X u U;simp_rw [fabled L K b' P];rfl
 have hS : S F=TA*∑ i,G'' i:=by
    unfold S;rw [hv']
    refine sonicF (G:=G) G' (pal f) TA ?_ (fun i=>(hψ i).fit); intro i
    have hz:=show RowCost τ U X (Q+1) from fun i j=> (hK ..).trans (ENNReal.ofReal_le_ofReal (by linarith only : Q ≤ Q+1))
    obtain ⟨hy,z,ha,hk,hd',hp'⟩:=ferry_lives (P e n) hz (by linarith) ht hs (hX _ hr) hT hp.coherent i
    exact ⟨d,z,ha,hk,hy,hd',hp'⟩
 have he (k:ℕ)(hK:k≤h): a'^h*u^k=a'^(h-k):=by
    change a'^h*a'⁻¹^k=_; rw [← Nat.sub_add_cancel hK,pow_add,inv_pow]; -- rewrites h-k on RHS?rw includes RHS h
    rw [Nat.add_sub_cancel_right];field_simp
 constructor
 · rw [hS,abs_mul,abs_of_nonneg hAA];apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum (g:=fun _=>Y') fun i _=>(HE i).1)) hAA).trans
   rw [sum_const,card_univ,nsmul_eq_mul]; apply le_of_eq
   change TA*(c*(C*((Q+V)^n*B+D*u^w)*(∏ i,a i)))=C*((Q+V)^n*B*a'^h+D*a'^(h-w))*(∏ i,a i)
   rw [←he _ hw,←mul_assoc,show TA*c=a'^h from div_mul_cancel₀ _ hc.ne'];ring
 intro he' H0;rw [hS]; have hy(i:α):G'' i=u^(q+∑ i,b i)*S P:=(HE i).2 he' H0
 simp_rw [hy];rw [sum_const,card_univ,nsmul_eq_mul]
 change TA*(c*(u^_*_))=a'^_ *_
 rw [← he _ hb,←mul_assoc,show TA*c=a'^h from div_mul_cancel₀ _ hc.ne'];ring
end YM.RG08.Halo

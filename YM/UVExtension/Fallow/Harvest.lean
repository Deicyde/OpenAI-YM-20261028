import YM.UVExtension.Fallow.Coal
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {S:Schedule}{s:Side}{G:Gauge}{C:Family G}{N p n:ℕ}
-- leakage to offDiag within.R.Torus. Any table.
lemma carried (n:ℕ)(k:ℕ) : ∀ᶠ i in atTop,(n:ℝ)*(2*(3*(S.a i)))<S.a k:=
    (show Tendsto (fun i=> (n:ℝ)*(2*(3*S.a i))) atTop (𝓝 0) from by simpa only [mul_zero] using (((S.shrinks.const_mul (3:ℝ)).const_mul (2:ℝ)).const_mul (n:ℝ))).eventually (gt_mem_nhds (S.a_pos k))
variable (H: Vintage.YM.Family.Makes C)(F:Fin n→ Stem C p)(A:Set (Points n))(hx:IsCompact A)(hv:A⊆ NoHit C.S p n)
include H hx hv
lemma stalk (h:∀ i,Crude C (F i)): ∃ b:ℝ,0 ≤ b∧∀ᶠ N:ℕ in atTop, ∀ o, Extraction.tag (C.S.a N) o ∈ A → ‖patch F N o‖ ≤ b:=by
   obtain ⟨y,hy,hY⟩:= Gaps.some C.S p hx hv; obtain ⟨m,hm⟩:= (C.S.shrinks.eventually (gt_mem_nhds hy)).exists
   obtain ⟨k,hk,hK,H'⟩:= ((eventually_ge_atTop m).and ((carried n m (S:=C.S)).and (eventually_all.mpr fun i=> (h i).2))).exists
   choose L hL using H'; let b:= ∏ i,L i
   refine ⟨|b|,abs_nonneg _,?_⟩
   filter_upwards [eventually_all.mpr hL, eventually_ge_atTop k,eventually_all.mpr fun i=> (h i).1.vistas k] with i hi he ht o ho
   have hp:= hY _ ho
   exact (reckoned H _ L k hk he hK (fun j=> ⟨(ht j).choose_spec,hi j⟩) _ fun i j hj=> lt_of_lt_of_le hm (Gaps.gridSeparation C.S _ rfl hp j i hj.symm)).trans (le_abs_self b)

lemma losing (h:∀ i,Crude C (F i))(j:Fin n)(he:Faded C (F j))(ε:ℝ)(hh:0<ε) : ∀ᶠ N:ℕ in atTop, ∀ o,Extraction.tag (C.S.a N) o∈A→ ‖patch F N o‖ ≤ ε:=by
   obtain ⟨y,hy,hY⟩:= Gaps.some C.S p hx hv; obtain ⟨m,hm⟩:= (C.S.shrinks.eventually (gt_mem_nhds hy)).exists
   obtain ⟨k,hk,hK, H',hZ⟩:= ((eventually_ge_atTop m).and ((carried n m (S:=C.S)).and (he.2.and (eventually_all.mpr fun i=> (h i).2)))).exists
   choose L hL using hZ
   let r:= ∏ i∈Finset.univ.erase j,L i; let t:= ε/(1+|r|); have hp:0<t:=by unfold t; positivity
   let Y i:= if i=j then t else L i
   have ht : ∏ i,Y i ≤ ε:=by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ _),show Y j=t from if_pos rfl, show (∏ i∈Finset.univ.erase j,Y i) = r from Finset.prod_congr rfl fun i hi=> if_neg (mem_erase.mp hi|>.1)]
      refine (mul_le_mul_of_nonneg_left ((le_abs_self r).trans (le_add_of_nonneg_left zero_le_one)) hp.le).trans_eq ?_; exact div_mul_cancel₀ _ (by positivity)
   filter_upwards [eventually_ge_atTop k,H' _ hp,eventually_all.mpr hL,eventually_all.mpr fun i=> (h i).1.vistas k] with N hn hh hl hd o ho; refine (reckoned H F Y k hk hn hK (fun i=> ⟨(hd i).choose_spec,?_⟩) _ (fun i j hij=> lt_of_lt_of_le hm (Gaps.gridSeparation C.S _ rfl (hY _ ho) j i hij.symm))).trans ht; unfold Y; split; next h=> exact h ▸ hh
   next h=> exact hl i

omit H in
lemma fading (h:∀ i,Pasted (F i))(j:Fin n)(he:Cloud C (F j)) : ∀ᶠ N:ℕ in atTop,∀ o,Extraction.tag (C.S.a N) o∈A→ patch F N o=0:=by
   obtain ⟨r,hr⟩:= he.silent; choose y hy using h
   let V:= Finset.univ.sup y; have hv(i): y i≤ V:= Finset.le_sup (s:=Finset.univ) (f:=y) (mem_univ i)
   obtain ⟨s,hs,hS⟩:=Gaps.some C.S p hx ‹_›; have ht: ∀ᶠ N:ℕ in atTop, C.S.a N*(↑(r+V:ℕ):ℝ)<s:=by have hz := C.S.shrinks.mul_const (↑(r+V:ℕ):ℝ); rw [zero_mul] at hz; exact hz.eventually (gt_mem_nhds hs)
   filter_upwards [ht,hr,eventually_all.mpr hy] with N ht hr h o ho
   let X:= wrap (C.side N p) ∘ o
   have he(i)(hi:i≠j): r+V< separation (X j) (X i):=by
       exact_mod_cast (lt_of_mul_lt_mul_left (lt_of_lt_of_le ht (Gaps.gridSeparation C.S X rfl (hS _ ho) i j hi)) (C.S.a_pos _).le)
   let Y i:= bloom (F i N) (X i); let W U:=∏ i∈Finset.univ.erase j,Y i U
   have hh(a)(hp:a≠j): Interior (Mark.Outer r (X j)) (Y a):=by
      have ht:= translated_window (X a) ((h a).enlarges (window_large (hv a))); rw [zero_add] at ht; refine ht.enlarges (fun x hx=>?_); obtain ⟨v,hv,rfl⟩:= hx
      let x:= wrap (C.side N p) v+ (X a); have hh:= Work.E08.separation_box_add (X a) hv
      have hS:= separation_triangle (X j) x (X a); have ht : separation x (X a)≤V:= by rw [separation_comm]; exact hh
      change r< separation x (X j); rw [separation_comm]; have hx:= he a hp; omega
   unfold patch garden; simp_rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]; -- warning simp loop
   exact hr (X j) W (Interior.combines Y _ (fun i hi=> hh i (Finset.mem_erase.mp hi|>.1)))

omit H hx hv
lemma angel (F V: Fin n→ Stem C p)(j:Fin n)(T:Stem C p)(h:F j=V j+T)(hx:∀ i,i≠j→F i=V i)(hp:∀ i,Pasted (V i))(hv:Pasted T): ∀ᶠ N:ℕ in atTop,∀ o,patch F N o=patch V N o+patch (update V j T) N o:=by
   filter_upwards [eventually_all.mpr fun i=>(hp i).blast,hv.blast] with N hn hv o; let X:=wrap (C.side N p) ∘ o; let β:= C.beta N p
   let Y i:= bloom (V i N) (X i); let A:= bloom (T N) (X j); let Z U:=∏ i∈Finset.univ.erase j,Y i U
   have he(i): Envelope (Y i):= (hn i).comp_env (law_translate 0 _).measurable
   have hZ: Envelope Z:= Envelope.prodC _ _ fun i _=>he i; have hA : Envelope A := hv.comp_env (law_translate 0 _).measurable
   have hx(s : Fin n→ Stem C p)(h:∀ i,i≠j→s i=V i): patch s N o=moment β (fun U=>bloom (s j N) (X j) U*Z U):=by
      refine congr_arg (moment β) (funext fun U=>?_); change (∏ i,bloom (s i N) (X i) U)=_; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]; exact congr_arg (_* ·) (Finset.prod_congr rfl fun i hi=>congr_arg (fun s : Stem C p=> bloom (s N) (X i) U) (h i (Finset.mem_erase.mp hi|>.1)))
   rw [hx F ‹_›, hx V (fun i _=>rfl),hx (update V j T) (fun i hi=> Function.update_of_ne hi ..),h,Function.update_self]; unfold moment; rw [← integral_add (((he j).mulC hZ).integrableC _) ((hA.mulC hZ).integrableC _)]; refine integral_congr_ae ?_; filter_upwards with U; exact add_mul ..
include hx hv in
lemma replace (V:Fin n→ Stem C p)(hp:∀ i,Pasted (V i))(hP:∀ i,Pasted (F i))(hs:∀ i,Cloud C (F i-V i)): ∀ᶠ N:ℕ in atTop,∀ o,Extraction.tag (C.S.a N) o∈A→ patch F N o=patch V N o:=by
   let M (s:Finset (Fin n)) i:= if i∈s then F i else V i; have hM (s i): Pasted (M s i):=by unfold M; split; exact hP _; exact hp _
   have he (s: Finset (Fin n)): ∀ᶠ N:ℕ in atTop,∀ o,Extraction.tag (C.S.a N) o∈A→ patch (M s) N o=patch V N o:=by
      induction s using Finset.induction with
      | empty=> filter_upwards with N; simp [M]
      | insert i s hi ih=>
          let X:= F i-V i; let Y:= update (M s) i X; have hY j:Pasted (Y j):=by
            by_cases h:i=j; · subst j; rw [show Y i=X from Function.update_self ..]; exact (hs _).same
            rw [show Y j=M s j from Function.update_of_ne (Ne.symm h) ..]; exact hM .. 
          have hz:Y i = X:=Function.update_self ..
          have h':=angel (M (insert i s)) (M s) i X (by simp [M,hi,X,add_comm]) (fun j hj=> by simp [M,hj]) (hM s) (hs i).same
          filter_upwards [ih,h',fading Y A hx hv hY i (hz.symm ▸ hs i)] with N h1 h2 h3 o ho; rw [h2 o, show patch _ N o= _ from h3 _ ho,h1 o ho,add_zero]
   have hh:= he Finset.univ; rw [show M Finset.univ=F by funext i; simp [M]] at hh; exact hh
include H hx hv
lemma cover (h:∀ i, Wealth C (F i)) : ∃ b:ℝ,0 ≤ b∧∀ᶠ N:ℕ in atTop, ∀ o, Extraction.tag (C.S.a N) o ∈ A → ‖patch F N o‖ ≤ b:=by
   choose V hP hp using fun i=> (h i).2; obtain ⟨b,hb,hS⟩:= stalk H V A hx hv hP; refine ⟨b,hb,?_⟩; filter_upwards [hS,replace F A hx hv V (fun i=> (hP i).1) (fun i=>(h i).1) hp] with i hi hx o ho; rw [hx o ho]; exact hi o ho
end YM.UVExtension.Fallow

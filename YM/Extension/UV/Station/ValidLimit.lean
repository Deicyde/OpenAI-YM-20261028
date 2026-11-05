import YM.Extension.UV.Station.Pages
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Lattice RG Push.PriceCompiler Filter Function
open scoped Topology BigOperators Classical Pointwise
variable {κ:Type*} {σ:ℝ} {l:κ→ℕ}
lemma read_moments_pair (τ:ℝ) (hτ:τ<σ) (f g:κ→ℝ) {C D:ℝ} (h:tight.mass f σ l C) (hg:∀ i, |g i| ≤ D*Real.exp (τ*l i)) : Summable (fun i=>|f i*g i|) ∧ |∑' i, f i*g i| ≤ tight.read f τ l *D:= by
   set z := fun i:κ=> |f i| *Real.exp (τ*l i)
   have ht₀ i : z i ≤ |f i| *Real.exp (σ*l i):=by unfold z; gcongr
   have ht: Summable z := h.2.1.of_nonneg_of_le (fun _=> by unfold z; positivity) ht₀
   have he i : ‖f i*g i‖ ≤ D*z i:= (show |f i*g i| ≤ _ from by unfold z; rw [abs_mul,mul_left_comm]; apply mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)) -- z let unfold warning
   have hv:=(ht.mul_left D).of_nonneg_of_le (fun _=>norm_nonneg _) he
   exact ⟨hv,(norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum he (ht.mul_left D)).trans_eq (by rw [tsum_mul_left,mul_comm];rfl))⟩
lemma functional (f : ℕ→κ→ℝ) (x: κ→ℝ) {τ:ℝ} (hτ:τ<σ) (l:κ→ℕ) (s:∀ M:ℕ,Set.Finite {i| l i≤M}) {C:ℝ} (h:∀ᶠ i:ℕ in atTop,tight.mass (f i) σ l C) (hf:Tendsto f atTop (nhds x)) (g : κ→ℝ) (D:ℝ) (hg:∀ i, |g i| ≤ D*Real.exp (τ*l i)) : Tendsto (fun n=>∑' i,f n i*g i) atTop (nhds (∑' i,x i*g i)):=by
    let L(f:κ→ℝ):=∑' i,f i*g i
    suffices he:Tendsto (fun n=>|L (f n)-L x|) atTop (nhds 0) by exact tendsto_iff_dist_tendsto_zero.mpr he
    have hx:= tight.mass_closed h hf; have he := tight.strict_limit h hf s hτ
    apply squeeze_zero' (Eventually.of_forall fun _=>abs_nonneg _) _ (by simpa only [zero_mul] using he.mul_const D)
    filter_upwards [h] with n hn
    have hK f {u:ℝ}(h:tight.mass f σ l u) := read_moments_pair τ hτ f g h hg
    have hZ (f) (hn:tight.mass f σ l C) : Summable fun i=> f i*g i:=Summable.of_norm (hK _ hn).1
    have hh := ((hZ _ hn).hasSum.sub (hZ _ hx).hasSum)
    rw [show L (f n)-L x=L (f n-x) from Eq.trans hh.tsum_eq.symm (tsum_congr (fun i=> by rw [Pi.sub_apply, sub_mul]))]
    exact (hK _ (tight.sub hn hx)).2


lemma limits_sum {F: ℕ → κ → ℝ} {f:κ →ℝ} {L:ℝ} (h:∀ᶠ n:ℕ in atTop,SumBudget (F n) L) (hf:Tendsto F atTop (nhds f)): SumBudget f L:=by
   have hb:=tight.mass_closed (l:=fun _=>0) (σ:=0) (C:=L) (show ∀ᶠ n:ℕ in atTop,tight.mass (F n) 0 (fun _=>0) L from by filter_upwards [h] with n hn; simpa only [tight.mass,zero_mul,Real.exp_zero,mul_one,fun k=>abs_of_nonneg (show 0≤F n k from hn.1 k)] using hn) hf -- abs requires simp_rw
   apply budget_minor (fun i=> ge_of_tendsto (tendsto_pi_nhds.mp ‹Tendsto F _ (nhds f)› i) (h.mono fun n hn=>hn.1 i)) (fun i=>le_abs_self (f i)) (g:=fun x=>|f x|) (by simpa [tight.mass] using hb)

variable {G:Gauge} (x:BookKey G→ℝ)
    {σ A L:ℝ}{p:Clip}(R:ℕ→PathData G) (h:∀ᶠ n:ℕ in atTop,(R n).Bounds p σ A L) (ht:Tendsto (book_get ∘ R) atTop (nhds x))
include h ht
lemma entry_row (b:PlaqAxes) : tight.mass (fun i:Slot=>x (.inl (b,i))) σ (fun i=>i.length) A := tight.mass_closed (F:=fun n i=>book_row (R n) b i) (h.mono fun n hn=>row_budget _ hn _) (tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp ht (.inl (b,i)))
lemma path_mass : PathMass (book_path x) σ A L A A:= by
  obtain ⟨n,hn⟩:= h.exists
  /- have hg (k b) := tight.mass_closed (F:=fun n s=>book (R n) k s b) (h.mono fun _ hi=>book_budget _ hi _ _) (tendsto_pi_nhds.mpr fun s=> tendsto_pi_nhds.mp ht (.inr ⟨k,b,s⟩))
  -/
  have ha (k:Fin 3) : SumBudget (fun i=> (payload x k i).budget σ) (cap k A L) := by
    let q:=k.val+2; letI : NeZero q:=⟨by omega⟩
    have hw (f:BookKey G → ℝ) i: (payload f k i).budget σ = ∑ b:Colors G k, |(f (.inr ⟨k,b,(slots q i)⟩))| * Real.exp (σ*pat_len (slots q i)):= by rw [← Finset.sum_mul]; rfl
    apply limits_sum (F:=fun n i=> (payload (book_get (R n)) k i).budget σ) _ (tendsto_pi_nhds.mpr fun i=> ?_)
    · filter_upwards [h] with n hn
      fin_cases k <;> first | exact (compact_mass _ hn).loop | exact (compact_mass _ hn).cubic | exact (compact_mass _ hn).quartic
    simp_rw [hw]; exact tendsto_finsetSum _ fun b hb=> (continuous_abs.continuousAt.tendsto.comp (tendsto_pi_nhds.mp ht (.inr ⟨k,b,slots _ i⟩))).mul_const _
  exact ⟨hn.width,fun i=>Stationary.budget_copy roster (entry_row x R h ht i),ha 0,ha 1,ha 2⟩
lemma path_invariant (k:Fin 3) i : ((payload x k i)).Invariant:= by
  haveI : NeZero (k.val+2):= ⟨by omega⟩
  have hv (y) : Tendsto (fun n=> (payload (book_get (R n)) k i).poly y) atTop (nhds ((payload x k i).poly y)) := by
    unfold Atom.poly; apply tendsto_finsetSum; intro b hb
    exact (tendsto_pi_nhds.mp ht (.inr ⟨k,b,slots _ i⟩)).mul_const _
  intro t a; refine tendsto_nhds_unique_of_eventuallyEq (hv _) (hv _) ?_
  filter_upwards [h] with n hn
  have H:=(compact_bounds _ hn).invariant i
  fin_cases k <;> first | exact H.1 t a | exact H.2.1 t a | exact H.2.2 t a

lemma row_symbol (b d:PlaqAxes): Tendsto (fun n=>(compactify (R n)).symbol0 b d) atTop (nhds ((book_path x).symbol0 b d)):=by
    obtain ⟨n,hn⟩:=h.exists
    let w (s:Slot):ℝ:=if s.plaq=d then 1 else 0
    have hg y : (book_path (G:=G) y).symbol0 b d=∑' i:Slot, y (.inl (b,i))*w i:= by
       unfold PathData.symbol0; simp_rw [w,mul_ite,mul_zero,mul_one]; exact (roster).tsum_eq (fun i:Slot=>if i.plaq=d then y (.inl (b,i)) else 0)
    simp_rw [compactify,hg]
    let f(n:ℕ)(s:Slot):=book_row (R n) b s
    exact functional f _ (half_lt_self hn.width) (fun i:Slot=>i.length) (fun M=>Set.finite_coe_iff.mp (by exact (slot_roster M))) (by filter_upwards [h] with n hn; exact row_budget _ hn _) (tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp ht (.inl (b,i))) w 1 (fun i=> by dsimp [w]; split_ifs <;> [simpa using Real.one_le_exp (show 0≤ σ/2*i.length by have :=hn.width;positivity); simpa using Real.exp_nonneg (σ/2*i.length)])

private def cuts (b:Fin 2→PlaqAxes) (u:Pattern 2) : ℝ:=if (fun i=>(u i).plaq)=b then 1 else 0
lemma loop_functional (w:Pattern 2→ℝ) {C:ℝ} (hp : ∀ s, |w s| ≤ C*Real.exp ((σ/2)*(pat_len s))) (b:Fin 2→PlaqAxes) (o:Fin 2→G.ColorIndex):
 Tendsto (fun i=>∑' n, (compactify (R i)).loop_coeff b o n * w (slots _ n)) atTop (nhds (∑' n, (book_path x).loop_coeff b o n*w (slots _ n))) := by
   obtain ⟨n,hn⟩:=h.exists
   have he y: (∑' n, (book_path y).loop_coeff b o n*w (slots _ n))=∑' s:Pattern 2, y (.inr ⟨0,o,s⟩) * (cuts b s*w s):= by
      simp only [cuts,PathData.loop_coeff,ite_mul,mul_ite,mul_zero,one_mul,zero_mul]; exact (slots 2).tsum_eq (fun s:Pattern 2=> if (fun i=>(s i).plaq)=b then y (.inr ⟨0,o,s⟩)*w s else 0)
   simp_rw [compactify,he]
   apply functional (fun n s=>book (R n) 0 s o) _ (half_lt_self hn.width) pat_len (pattern_roster _) (C:=cap 0 A L) (by filter_upwards [h] with n hn; exact (book_budget _ hn _ _)) (tendsto_pi_nhds.mpr fun s=>(tendsto_pi_nhds.mp ht (.inr ⟨0,o,s⟩))) _ C (fun i=>by dsimp [cuts]; split_ifs <;> [simpa using hp i; simpa using (abs_nonneg _).trans (hp i)])
lemma loop_limits : (book_path x).loop_jets:= by
   obtain ⟨n,hn⟩:=h.exists
   have hD:= hn.width
   let s : ℕ ≃ Pattern 2:= slots _
   have h1 i : ((book_path x).loop i).leg= slots _ i:=rfl
   let w(l:Axis)(p:Pattern 2):ℝ:=((p 1).offset l-(p 0).offset l:ℤ)
   have hw (l p): |w l p| ≤ (momentFactor 1 (σ/2))*Real.exp ((σ/2)*pat_len p):=by
      have hz : |w l p| ≤ (book_path x |> fun r=>(r.loop (s.symm p)).length) :=by
         have he:=loop_offset_le ((book_path x).loop (s.symm p)) l; rw [h1,s.apply_symm_apply] at he
         dsimp [w]; have hm : |((p 1).offset l) - (p 0).offset l| ≤ ((book_path x).loop (s.symm p)).length := by rw [←Int.natCast_natAbs]; exact_mod_cast he
         exact_mod_cast hm
      exact hz.trans (show (pat_len (s (s.symm p)):ℝ) ≤ _ from by rw [s.apply_symm_apply]; apply (le_trans ?_ (pays_moment _ _ (show 0<σ/2 by positivity))); simp)
   intro b o
   constructor
   · have ht:= loop_functional x R h ht (fun _=>1) (C:=1) (by simp only [abs_one,one_mul]; exact fun _=>Real.one_le_exp (by positivity)) b o
     simp only [mul_one] at ht
     exact tendsto_nhds_unique_of_eventuallyEq ht tendsto_const_nhds (h.mono fun _ hi=> (loop_normal _ hi b o).1)
   intro l; exact tendsto_nhds_unique_of_eventuallyEq (loop_functional x R h ht (w l) (hw l) b o) tendsto_const_nhds (h.mono fun _ hi=> (loop_normal _ hi b o).2 l)
lemma limit_bounds : (book_path x).Bounds p σ A L:=by
   refine (path_mass x R h ht).bounds ⟨fun i=>⟨path_invariant x R h ht 0 i, path_invariant x R h ht 1 i,path_invariant x R h ht 2 i⟩,?_,loop_limits x R h ht⟩ le_rfl le_rfl le_rfl
   intro u v
   let F (r : PathData G):= (if u=v then p.direct else 0) + (∑ k,r.symbol0 k u*r.symbol0 k v)
   exact tendsto_nhds_unique_of_eventuallyEq (f:=fun i=> F (compactify (R i))) (tendsto_const_nhds.add <| tendsto_finsetSum _ (fun k _=> (row_symbol x R h ht k u).mul (row_symbol x R h ht k v))) (tendsto_const_nhds (x:=(if u=v then 1 else 0))) (h.mono fun _ hn=> (compact_bounds _ hn).metric u v)
end YM.Extension.UV.StationaryData

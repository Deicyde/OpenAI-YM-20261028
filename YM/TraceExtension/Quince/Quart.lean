import YM.TraceExtension.Quince.Shift
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push.Local (Probe)
open Push Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free Laurent Cub Finset
open MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n c f:Side}
variable {k p d r j u:ℕ}{B:BudgetPoint}{S:StepData c f}{T:Tube G S}
variable {X:Support f}{Y:Support c}{b m N i:ℕ}{σ M z t K w:ℝ}{Q: Probe G d}(H:Hol G){O:Config G f→ℝ}(hp:B.Regular X O)(hf:B.supBounds 0 X O w)(G':Rights G N)
   (hV:T.R.A0.strip σ M)(hσ:0<σ)(hM:0≤M)(hK:1≤K)(hk:0<z)(hi:20*(m+b+1)< c.val)(hh:∀ i∈X,halo b {S.ratio.parent i}⊆ Y)(hY:∀ i∈Y,separation 0 i ≤ m)
variable (hb:Peak.lit 0 X O d)(hB:d≤ N)(ht:N≤B.order)(hS:∀ k≤d,Carries (Ramble.lamina Q k B.threshold t) (d*k) K)
def δℓ (σ:ℝ)(k m b:ℕ)(K M:ℝ):= 4*(Real.exp (-(σ/2)*b)*(K+K)*(1+4*(m:ℝ))^k*widthCost (σ/2) k*M)
def εℓ (σ:ℝ)(d m b:ℕ)(K M:ℝ):=∑ k∈range (d+1),δℓ σ (d*k) m b K M
lemma δℓ_pos (b m k:ℕ) (hs:0<σ)(h:0≤K)(hM:0≤M):0≤δℓ σ k m b K M:=by unfold δℓ; have hx:=widthCost_ge (half_pos hs) k; positivity
lemma εℓ_pos (b m d:ℕ) (hs:0<σ)(h:0≤K)(hM:0≤M):0≤εℓ σ d m b K M:=Finset.sum_nonneg fun i _=>δℓ_pos _ _ _ hs h hM
local notation "C0"=> εℓ σ d m b K M
-- incoming fields bound. m head scope, input X accordingly lim.
def horn₀ (d k m:ℕ)(L:Side)(σ K M:ℝ):= 4*K*widthCost σ (d*k)*M*(1+4*depthW L m :ℝ)^(d*k)
def corn₀ (d m:ℕ)(L:Side)(σ K M:ℝ):=1 + ∑ i∈range (d+1),horn₀ d i m L σ K M
lemma horn_pos (d k m:ℕ) (L:Side)(h1:0<σ)(h2:0≤K)(h3:0≤M):0 ≤ horn₀ d k m L σ K M:=by unfold horn₀; have hv:=widthCost_ge h1 (d*k); positivity
lemma corn_pos (d m:ℕ)(L:Side)(h1:0<σ)(h2:0≤K)(h3:0≤M):1 ≤ corn₀ d m L σ K M:=le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>horn_pos d i m L h1 h2 h3))
local notation "C1"=> corn₀ d m S.patch.L σ K M
include hσ hV hM hK hi hh hY hS
lemma reachbound (j:Bond f)(he:j.1∈X)(k:ℕ)(hk:k≤d): ‖ownQ Q k m T t B.threshold j‖ ≤ C1:=by
    unfold ownQ; let K0:=horn₀ d k m S.patch.L σ K M
    have hv:= field_cost hσ hM hV _ (hS k hk)
    apply (hv.2 (lift j.1) j.2).trans; refine le_trans (b:=K0) ?_ (le_trans (Finset.single_le_sum (f:=fun k=> horn₀ d k m S.patch.L σ K M) (fun a _=>horn_pos _ _ _ _ hσ (by positivity) hM) (mem_range.mpr (Nat.lt_succ_of_le hk))) (le_add_of_nonneg_left zero_le_one))
    unfold K0 horn₀ liftCost; have hx : size (lift j.1) ≤ 4*depthW S.ratio.count m:= by
       apply Flutes.cards; have hv:= facesBound hh hY _ he; rw [separation_comm] at hv; simpa only[sub_zero] using Work.E08.lift_mem_box hv
    have ht:=widthCost_ge hσ (d*k); gcongr; exact_mod_cast (show size (lift j.1) ≤ 4*depthW S.patch.L m from hx)
include hp hf hk ht hB hb
open Peak
lemma zert (ℓ:ℕ)(h'ℓ:ℓ ≤ d)(P:Flight p u)(he:HEq T.R.A0 (linesOf P z))(hℓ:S.patch.L=P.L)(hr:4≤ u)(hy:d≤p) (he':C0 ≤ C1):
    ‖iteratedDeriv ℓ (dimW 0 m T O ∘ H.testLinks d 0 (t • Q.1)) 0‖ ≤ (Fintype.card (OrderedFinpartition ℓ):ℝ) * (2:ℝ)^ℓ*(C0*C1^ℓ*G'.fee)*w:=by
   let R:=poleQ Q H m T t B.threshold; let V:= B.threshold • R; let g:=O ∘ increment (1:Config G f)
   have hQ : dimW 0 m T O ∘ H.testLinks d 0 (t • Q.1) = g ∘ V:=by
       funext i; apply congr_arg g (meant_o H Q m T B.threshold_pos i)
   have hu:0≤ C0:= εℓ_pos _ _ _ hσ (zero_le_one.trans hK) hM
   have h₁ := corn_pos d m S.patch.L hσ (zero_le_one.trans hK) hM
   have hv:= poleQs H Q m T t B.threshold |>.const_smul B.threshold
   have hsV(k:ℕ): iteratedDeriv k V 0=B.threshold • iteratedDeriv k R 0 := (by apply iteratedDeriv_const_smul; exact (poleQs H Q m T t _).of_le le_top)
   have hw: V 0=0:=by unfold V R; rw [Pi.smul_apply,poleQ_0,smul_zero]
   have hG: ContDiffAt ℝ d g (V 0):=by rw [hw]; exact (hp.smooth 1 (one_healthy _ _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr (hB.trans ht))
   rw[hQ]; rw [show iteratedDeriv ℓ (g ∘ V) 0= _ from (Cases.compReads (n:=ℓ) hG (show ContDiffAt ℝ d V 0 from hv.of_le le_top) (Nat.cast_le.mpr h'ℓ) (fun _=> 1))]; let v:= C0*C1^ℓ*G'.fee*w
   refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> show ‖Cases.caseRead i _ _ _ _‖ ≤ (2:ℝ)^ℓ * v from ?_)).trans ?_)
   · let y (k:ℕ):=ownQ Q k m T t B.threshold; let q:=i.partSize; let g':Fin i.length→ Directions G f:= fun j=> iteratedDeriv (q j) V 0; have hE:=hf.1; have hp:= G'.large
     have htℓ(j): q j ≤ d:=(i.partSize_le j).trans h'ℓ
     unfold Cases.caseRead; rw [hw]; change ‖iteratedFDeriv ℝ i.length g 0 g'‖ ≤ _; unfold g'; simp_rw[hsV]
     have hz : ∑ j,q j=ℓ:=by simpa using i.sum_sigma_eq_sum (fun _ => (1:ℕ))
     have hsig(j): Mom.screen X (B.threshold • y (q j))∈ Mom.Maps 0 X (q j):=by
         have ha (L:Side)(Z:Lines L)(h:HEq Z (linesOf P z))(hK:L=P.L): ∃ r∈ Place.rangeLt (Axis→G.Color) (q j), applyLine Z (Ramble.lamina Q (q j) B.threshold t)=verdict r :=by
             subst L; rw [eq_of_heq h]; exact city_p Q t _ _ P hk hr ((htℓ j).trans hy)
         obtain ⟨r,h,h'⟩:=ha S.patch.L T.R.A0 he hℓ; rw [map_smul]; apply (Mom.Maps _ _ _).smul_mem; refine map_city _ h (fun e _=> congr_fun (congr_fun h' (lift e.1)) e.2)
     have hδ(a)(e:Edge (Site f))(h:Mom.needed X e): ‖iteratedDeriv (q a) R 0 e-y (q a) e‖ ≤ C0:=
         LE.le.trans (clarity H hV hσ hM hi hh hY (hS (q a) (htℓ a)) e h.1) (Finset.single_le_sum (f:=fun i=>δℓ σ (d*i) m b K M) (fun j _=>δℓ_pos _ _ _ hσ (by positivity) hM) (mem_range.mpr (Nat.lt_succ_of_le (htℓ a))))
     apply (weigh_inputs ‹B.Regular X O› hf G' ((i.length_le.trans h'ℓ).trans hB) ht h₁ hu he' (hb _ q _ (hz.le.trans h'ℓ) (fun i'=>⟨i.partSize_pos _,hsig i'⟩)) (fun j e he=> reachbound hV hσ hM hK hi hh hY hS e he.1 _ (htℓ j)) hδ).trans; unfold v; gcongr <;> first|exact i.length_le|norm_num
   simp[v]; ring_nf; exact le_rfl
end YM.PhysicalNext.Repeat.Quince

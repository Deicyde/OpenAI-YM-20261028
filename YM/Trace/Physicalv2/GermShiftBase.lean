import YM.Planned.PRIMARY_INTEGRAL_295.FlatCancel

/-!
An upgrade for cancellation of a *true* gauge-cylinder error when comparing
field derivative stencils. Work on embedded cover supports at the placement
(this is used only on unmasked germs). Precompose on joint polynomial lists;
we do not claim links are independent or omit winding addresses. The use of
`Place.cancellation` from the checked construction allows *bidegrees up to d*,
needed on the difference of two shifts with endpoint smoothing degree one
higher; a constant test at a wrapping support alone would not license this.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 180000
set_option maxRecDepth 3500
noncomputable section
namespace YM.Trace.Physical.GermShift
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations MeasureTheory
open Source.Drops WardBin YM.Planned.PrimaryIntegral295 Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{S T : Finset Cover}{k n:ℕ}
local notation "chart" => (fun A : Finset Cover => Place.pore (G:=G) (S:=A))

abbrev moved (S : Finset Cover) (b:Cover) : Finset Cover := S.image (fun x=> x+b)
variable {a:Cover}
noncomputable def moveSpot (h:moved S a⊆T)(x:Place.Spot S):Place.Spot T := ⟨(⟨(Place.first x).val+a,h (Finset.mem_image.mpr ⟨(Place.first x).val,(Place.first x).property,rfl⟩)⟩,Place.beam x),h (Finset.mem_image.mpr ⟨(Place.first x).val+step (Place.beam x),x.property,by exact add_right_comm ..⟩)⟩

noncomputable def clip (G:Gauge)(h:moved S a ⊆ T) : Place.Dev T G →L[ℝ] Place.Dev S G := ContinuousLinearMap.pi (fun p=>ContinuousLinearMap.proj (moveSpot h p))
lemma moved_edge (h:moved S a⊆ T)(x : Place.Spot S): Place.placeEdge (moveSpot h x) = ((Place.placeEdge x).1 + a, (Place.placeEdge x).2) := rfl
variable {V : Type*} {f : CoverConfig G → V}
lemma shift_local (hl : LocalOn S f)(a:Cover) : LocalOn (moved S a) (f ∘ translate a):=by
   intro U V h; apply hl; intro x h₁ h₂; exact h (x.1+a,x.2) (Finset.mem_image.mpr ⟨x.1,h₁,rfl⟩) (Finset.mem_image.mpr ⟨x.1+step x.2,h₂,by exact add_right_comm ..⟩)
lemma translated_masked (hl:LocalOn S f)(h:moved S a ⊆ T) : (f ∘ translate a) ∘ Place.pore (S:=T) = (f ∘ Place.pore (S:=S)) ∘ clip G h := by
   funext v; apply hl; intro e he he'
   let b : Place.Spot S:=⟨(⟨e.1,he⟩,e.2),he'⟩
   change Place.pore v (_,_) = Place.pore _ _
   have hz : Place.placeEdge b=e:=rfl
   have hE : Place.placeEdge (moveSpot h b)=(e.1+a,e.2) := moved_edge h b
   rw [←hE,←hz,Place.pore_site,Place.pore_site]
   exact rfl
lemma moved_zero : moved S (0:Cover) = S:= by simp only [moved,add_zero,Finset.image_id']
lemma gauge_shift (h:GaugeInvariant f) (a:Cover) : GaugeInvariant (f ∘ translate a):=by
    intro k U
    have hz : translate a (Lattice.gauge k U)= Lattice.gauge (fun i=>k (i+a)) (translate a U):=by funext i; change k _ * U _ * (k (i.1+a+step _))⁻¹ = _; unfold Lattice.gauge translate; rw [add_right_comm]
    exact (congr_arg f hz).trans (h _ _)
lemma restrict_ping (h:moved S a ⊆ T)(v:Place.Potential G) : clip G h (Place.ping T v)=Place.ping S (fun x=>v (x+Place.seat a)) := by
   ext1 i; change v (Place.seat ((Place.first i).val+a)) _ = _
   rw [Place.seat_add]; rfl
variable [NormedAddCommGroup V][NormedSpace ℝ V]
lemma moved_jet (h:moved S a ⊆ T)(hl:LocalOn S f){r:ℕ}(hf : ContDiffAt ℝ k (f ∘ Place.pore (S:=S)) 0)(hk : r ≤ k) (y:Fin r→Place.Potential G) :
   iteratedFDeriv ℝ r ((f ∘ translate a) ∘ Place.pore (S:=T)) 0 (fun i=>Place.ping T (y i)) = iteratedFDeriv ℝ r (f ∘ Place.pore (S:=S)) 0 (fun i=>Place.ping S (fun w=>y i (w+Place.seat a))):= by
      have hz x:= restrict_ping h (y x)
      rw [translated_masked hl h,jets_linear (clip G h) (hf.of_le (Nat.cast_le.mpr hk)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
      change iteratedFDeriv ℝ r (f ∘ Place.pore (S:=S)) 0 (fun i=>clip G h (Place.ping T (y i))) = _
      simp_rw [hz]
lemma moved_smooth (h:moved S a⊆T)(hl:LocalOn S f){k:WithTop ℕ∞}(hf:ContDiffAt ℝ k (f ∘ pore (S:=S)) 0):ContDiffAt ℝ k ((f ∘ translate a) ∘ Place.pore (S:=T)) 0 := by
    rw [translated_masked hl h]; apply ContDiffAt.comp
    · rwa [(clip G h).map_zero]
    exact (clip G h).contDiff.contDiffAt

variable {f:CoverConfig G→ℂ}
def Null (k:ℕ)(S:Finset Cover)(f:CoverConfig G→ℂ) : Prop := ∀ (r:ℕ) (w:Fin r→ℕ), (∑ i,w i)<k → r<k → ∀ y:Fin r → Place.Potential G, (∀ i,y i ∈ Place.rangeLt (Axis→G.Color) (w i)) → iteratedFDeriv ℝ r (f ∘ Place.pore (S:=S)) 0 (fun i=>Place.ping S (y i)) = 0

lemma flat_null (H:Hol G) (hf:ContDiffAt ℝ k (f ∘ pore (S:=S)) 0)(hl:LocalOn S f)(hg:GaugeInvariant f)(he : ∀ (J : Jet G) n, n ≤ k → leading n (fun t=> f (H.links k J t))=0) : Null (k+1) S f:= fun _r w h hk u hu=>Place.cancellation hl hg H hf (fun J n hn=>he J n (Nat.le_of_lt_succ hn)) (by omega) w h u hu

abbrev translatedSupport (a:Cover)(S:Finset Cover):=S ∪ moved S a
abbrev offsetDiff(f:CoverConfig G→ℂ) (a:Cover) : CoverConfig G→ℂ := fun U=> (f (translate a U)-f U)
private lemma translate_sub_mom {a:Cover}{r:ℕ}(k:ℕ)(H:Null k S f)(hk:r≤k)(w:Fin r→ℕ)(hw: (∑ i,w i) ≤ k)(y:Fin r→Place.Potential G)(hy:∀i, y i∈Place.rangeLt (Axis→G.Color) (w i)):
      let M:=iteratedFDeriv ℝ r (f ∘ Place.pore (S:=S)) 0
      M (fun i=>Place.ping S (fun x=>y i (x+Place.seat a))) = M (fun i=>Place.ping S (y i)) := by
   classical
   intro M
   let z (i:Fin r) (s:Bool) : Place.Potential G := if s then (fun x=>y i (x+Place.seat a)-y i x) else y i
   have hZ i : (fun x=>y i (x+Place.seat a)) = ∑ s:Bool,z i s:=by funext x; simp [Function.comp_apply,z,Finset.sum_apply,Fintype.sum_bool]
   let s₁ : Fin r→Bool:= fun _=>false
   have he (s : Fin r→Bool)(hs:s≠s₁) : M (fun i=> Place.ping S (z i (s i)))=0 := by
       by_cases h₀ : ∀ i, 0<w i
       · let b i:=if s i then w i-1 else w i
         obtain ⟨j,hj⟩ : ∃ j,s j=true:= Classical.byContradiction (fun h=>hs (funext (not_exists.mp h |> fun h => fun j => Bool.eq_false_of_not_eq_true (h j))))
         have hB : ∑ i,b i < ∑ i,w i:=Finset.sum_lt_sum (fun i _=> by unfold b; split <;> omega) ⟨j,Finset.mem_univ _, by unfold b; simp [hj]; have := h₀ j;omega⟩
         have hr : r ≤ ∑ i,w i:=by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ =>(1:ℕ)) (fun i _=>h₀ i)
         have hi (i): z i (s i) ∈ Place.rangeLt (Axis→G.Color) (b i):=by
            by_cases hs:s i
            · simp only [z,b,if_pos hs]
              exact Place.band_step (show y i ∈ Place.rangeLt (Axis→G.Color) (w i-1+1) by rw [Nat.sub_add_cancel (h₀ i)]; exact hy i) _
            simp only [z,b,if_neg hs]; exact hy i
         by_cases hk' : r<k
         · exact H r b (hB.trans_le hw) hk' _ hi
         -- r=k so at least one b i =0
         obtain ⟨i,hi'⟩ : ∃ i,b i=0:=by
             by_contra! hx
             have h := Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ =>(1:ℕ)) (g:=b) (fun i _=>Nat.pos_of_ne_zero (hx i))
             simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at h; omega
         apply M.map_coord_zero i
         specialize hi i; rw [hi',Place.rangeLt,Submodule.mem_bot] at hi
         rw [hi,map_zero]
       push Not at h₀; obtain ⟨i,hi⟩:=h₀
       have hi' : w i=0:=by omega
       specialize hy i; rw [hi',Place.rangeLt,Submodule.mem_bot] at hy
       apply M.map_coord_zero i
       unfold z; split <;> simp only [hy,map_zero,Pi.zero_apply,sub_self]
       exact (Place.ping S).map_zero
   have e₀(i): Place.ping S (z i (s₁ i))=Place.ping S (y i):=by unfold z s₁; rw [if_neg (by decide)]
   rw [show (fun i=>Place.ping S (fun x=>y i (x+Place.seat a)))=(fun i=>∑s:Bool, Place.ping S (z i s)) from funext fun i=> by rw [hZ i,map_sum], M.map_sum, Finset.sum_eq_single s₁ (fun i _ h=>he i h) (by simp)]
   simp_rw [e₀]

lemma translate_equal_jet {r:ℕ}(hl:LocalOn S f)(hf:ContDiffAt ℝ k (f ∘ pore (S:=S)) 0)(h:Null k S f)(hk:r≤k)
      (w:Fin r→ℕ)(hw: (∑ i,w i) ≤ k)(y:Fin r→Place.Potential G)(hy:∀i, y i∈Place.rangeLt (Axis→G.Color) (w i))
      (T:Finset Cover)(hS:S⊆T)(hT:moved S a⊆ T):
      iteratedFDeriv ℝ r ((f ∘ translate a) ∘ Place.pore (S:=T)) 0 (fun i=>Place.ping T (y i)) = iteratedFDeriv ℝ r (f ∘ Place.pore (S:=T)) 0 (fun i=>Place.ping T (y i)):= by
    have hv :Lattice.translate (0:Cover) = (id: CoverConfig G→_):= by funext U e; change U (e.1+0,e.2)=_; rw [add_zero];rfl
    have he:=fun (a:Cover)(ha:moved S a⊆T)=>moved_jet (r:=r) ha hl hf hk y
    calc _ = _ := he a hT
         _ = iteratedFDeriv ℝ r (f ∘ Place.pore (S:=S)) 0 (fun i=>Place.ping S (y i)) := translate_sub_mom k h hk w hw y hy
         _ = _ := by simpa only [hv, Place.seat_zero, add_zero, comp_id] using! (he 0 (show moved S 0 ⊆ T by rw [moved_zero]; exact hS)).symm
lemma diff_cancel (hl:LocalOn S f)(hf:ContDiffAt ℝ k (f ∘ pore (S:=S)) 0)(h:Null k S f)(a:Cover)(T:Finset Cover)(hS:S⊆T)(hT:moved S a⊆ T):
    ContDiffAt ℝ k (offsetDiff f a ∘ pore (S:=T)) 0 ∧ Null (k+1) T (offsetDiff f a) := by
    have hv :Lattice.translate (0:Cover) = (id: CoverConfig G→_):= by funext U e; change U (e.1+0,e.2)=_; rw [add_zero];rfl
    have hx:=moved_smooth (G:=G) hT hl hf
    have hz:=moved_smooth (f:=f) (a:=0) (T:=T) (by rw [moved_zero]; exact hS) hl hf
    rw [hv,Function.comp_id] at hz
    refine ⟨hx.sub hz,?_⟩; intro r w hw hk y hy
    have hk' : r ≤ k:= by omega
    change iteratedFDeriv ℝ r (((f ∘ translate a) ∘ Place.pore (S:=T)) - (f ∘ Place.pore (S:=T))) 0 _ = 0
    rw [iteratedFDeriv_sub_apply (hx.of_le (Nat.cast_le.mpr hk')) (hz.of_le (Nat.cast_le.mpr hk')),ContinuousMultilinearMap.sub_apply, sub_eq_zero]; exact translate_equal_jet hl hf h hk' w (by omega) y hy T hS hT
lemma diff_good (hl:LocalOn S f)(hg:GaugeInvariant f)(a:Cover) : LocalOn (translatedSupport a S) (offsetDiff f a) ∧ GaugeInvariant (offsetDiff f a) :=
   ⟨fun U V h=> congr_arg₂ HSub.hSub (shift_local hl a U V (fun x hx hy=>h x (Finset.subset_union_right hx) (Finset.subset_union_right hy))) (hl U V (fun x hx hy=>h _ (Finset.subset_union_left hx) (Finset.subset_union_left hy))), fun k U=>congr_arg₂ HSub.hSub (gauge_shift hg a k U) (hg _ _)⟩
end YM.Trace.Physical.GermShift

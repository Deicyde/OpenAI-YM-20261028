import YM.TraceExtension.Perfect.Wicker
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge}{c f:Side}{p u:Clip}{C R:PathData G}{T:StepData c f}{F: Forest T.ratio}{ρ: Bid.Dir G c→AxisChart G F}{α D A ℓ μ B S:ℝ}

/-- All scalar jets have zero origin through order one. -/
def loom (G:Gauge)(f:Side): Submodule ℝ (Peat G f) where
 carrier:=setOf fun Z=> Cleric Z ∧ braid (Z ∘ input G f) (fun _=>0) 0 1
 zero_mem':= ⟨(clergy _ _).zero_mem, fun i _=>rfl⟩
 add_mem' :=by
    rintro Z V ⟨hp,h⟩ ⟨hf,hY⟩; refine ⟨(clergy _ _).add_mem (x:=Z) (y:=V) hp hf,fun i hi=>?_⟩
    change iteratedFDeriv ℝ i ((Z ∘ _)+(V∘_)) _=_
    rw [iteratedFDeriv_add_apply (hp.dye.of_le le_top) (hf.dye.of_le le_top),h _ hi,hY _ hi,iteratedFDeriv_zero_fun, Pi.zero_apply,add_zero]
 smul_mem':=by
    rintro c a ⟨h,y⟩; refine ⟨(clergy _ _).smul_mem (x:=a) c h,fun i hi=>?_⟩
    change iteratedFDeriv ℝ i (c • (a ∘ input G f)) _=_
    rw [iteratedFDeriv_const_smul_apply, y _ hi, iteratedFDeriv_zero_fun, Pi.zero_apply, smul_zero]; exact h.dye.of_le le_top
-- patch apparatus
structure Dart (G:Gauge)(f:Side) where
 J:Axis→Axis→Site f→Peat G f
 Y:Axis→Site f→Gal G f
 E:Axis→Site f→Peat G f
 Q:Axis→Site f→Peat G f
 twist:Axis→Axis→Axis→Site f→Peat G f
namespace Dart
variable (X:Dart G f)(t:T.Choices)(L:Side)(hL:T.ratio.count=L)
variable (F ρ) in
def hum (S:Sheaf)(k:ℕ)(Z:Site f→Peat G f):= (L.val:ℝ)^k • verse S T.ratio (inheritJ F ρ ∘ Z)
variable (F ρ) in
def mel (S:Sheaf)(Z:Site f→Gal G f) := (L.val:ℝ)^5 • verse S T.ratio (inheritY F ρ t ∘ Z)
section
variable (F ρ)
private def pine : Peat G f →ₗ[ℝ] Peat G c where
 toFun:=inheritJ F ρ
 map_add':=fun _ _=> rfl
 map_smul':=fun _ _=>rfl
def plume : (Site f→Peat G f)→ₗ[ℝ] (Site f→Peat G c) where
 toFun:=fun z=> pine F ρ ∘ z
 map_add':=fun _ _=>rfl
 map_smul':=fun _ _=>rfl
def stanza (S:Sheaf)(k:ℕ) := ((L.val:ℝ)^k) • ((mixer (A:=Peat G c) S T.ratio).comp (plume F ρ))
lemma hum_o (S:Sheaf)(k:ℕ)(Z:Site f→Peat G f): hum F ρ L S k Z= stanza F ρ L S k Z:=rfl
lemma plume_elm(a:Axis)(Z:Site f→Peat G f): inheritJ F ρ ∘ elm a Z=elm a (inheritJ F ρ ∘ Z):=by
 funext x; change pine F ρ (elm a Z x)=elm a _ x
 unfold elm Pull.dTap; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,map_sub];rfl
include hL
lemma hum_flux (a:Axis)(Z:Site f→Peat G f): hum F ρ L (Sheaf.main L) 5 (elm a Z)=elm a (hum F ρ L (Sheaf.flux L a) 4 Z):=by rw[hum,plume_elm,pow_succ]; rw [mul_smul,elm_flux T.ratio L hL,hum,rate_elm,pow_succ]
lemma hum_twig (a:Axis)(Z:Site f→Peat G f): hum F ρ L (Sheaf.main L) 4 (twig a Z)= twig a (hum F ρ L (Sheaf.leafEdge L a) 3 Z):=by
 change (L.val:ℝ)^4 • verse _ _ (twig a (inheritJ F ρ ∘ Z))= sprig a ((L.val:ℝ)^3 • verse _ _ _)
 rw [twig_r T.ratio L hL,map_smul,smul_smul]; have hp:(L.val:ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp L.property); rw [pow_succ, mul_inv_cancel_right₀ hp];rfl
private lemma hum_loom (S':Sheaf)(a:ℕ)(Z:Site f→Peat G f)(h:∀ x,Z x∈loom G f)(hc:Critical F p C ρ)(ht:T.patch.Branches T.kernel G)(hp:C.Bounds p α D A)(he:PriceGap F p C ℓ)(hx:0<ℓ)(t:T.Choices)(x:Site c): hum F ρ L S' a Z x∈loom G c:=by
   unfold hum;rw[Pi.smul_apply]; refine (loom G _).smul_mem _ (verse_mem _ _ _ _ (fun i=> ?_) x)
   obtain ⟨h,h'⟩:= h i; change braid (Z i ∘ _) _ _ _ at h'; change Cleric (Z i) at h
   let V:=fun x=>(encamp F ρ x).1; let U:=fun x=> content (V x)
   have hv:Army V 0:= (camp_thaw hc).1; have hy:V 0=1:= congr_arg Prod.fst (encamp_zero hc); have h0:U 0=0:=by unfold U; rw[hy,content_one]
   have hh:=wove (w:=U) (a:=0) (h0.symm ▸ h') (h0.symm ▸ h.dye) (h0.symm ▸ (show ContDiffAt ℝ ω (fun _ : Link G f=> (0:ℝ)) 0 from contDiffAt_const)) (hv.logL hy)
   refine ⟨flashes t hc ht hp he hx h, braid.trans (braided (inspire.trans ?_)) hh⟩
   filter_upwards [(show Tendsto V _ (𝓝 1) from hy ▸ hv.cont.tendsto).eventually content_encodes] with x hh; exact congr_arg (Z i) hh.symm
private lemma mel_rain (S':Sheaf)(Z:Site f→Gal G f)(h:∀ x,Z x∈rains G f)(hc:Critical F p C ρ)(ht:T.patch.Branches T.kernel G)(hp:C.Bounds p α D A)(he:PriceGap F p C ℓ)(hx:0<ℓ)(x:Site c): mel F ρ t L S' Z x ∈ rains G c:=by
    apply (rains G c).smul_mem (x:=verse _ _ _ x); apply verse_mem; intro v; obtain ⟨h,p⟩:= h v
    refine ⟨flair t hc ht hp he hx h,?_⟩; change (inheritY F ρ t (Z v)) 1=0; unfold inheritY; rw [content_one,encamp_zero hc]; change shuttle _ _ _ _ (Z v 1)=_; rw [p,map_zero]
end

def trace (a:Axis) := (Sheaf.trail (A:=ℝ) L a).choose
lemma trace_travel (a:Axis)(M:Cover→Peat G c): Sheaf.take M (Sheaf.flux L a)= Sheaf.take M (Sheaf.main L) + Sheaf.take (Sheaf.take M (Dart.trace L a)) (Sheaf.Δ (Sheaf.v L a)):=by
   funext x v
   let p: Peat G c→ₗ[ℝ] ℝ:= LinearMap.proj v
   have h := (Sheaf.trail (A:=ℝ) L a).choose_spec.2.2 (p ∘ M); rw [← Sheaf.inherit,← Sheaf.inherit, ← Sheaf.inherit, ← Sheaf.inherit] at h
   exact congr_fun h x
section
variable (F ρ)
def down : Dart G c where
 J a b:= hum F ρ L (Sheaf.flux L a) 4 (X.J a b)
 Y a:= mel F ρ t L (Sheaf.main L) (X.Y a)
 E a:= hum F ρ L (Sheaf.main L) 5 (X.E a)
 Q a:= hum F ρ L (Sheaf.leafEdge L a) 3 (X.Q a)+hum F ρ L (Dart.trace L a) 4 (X.J a a)
 twist a b i:= hum F ρ L (Sheaf.leafEdge L i) 3 (X.twist a b i)+(if i=a then hum F ρ L (Dart.trace L a) 4 (X.J a b) else 0)-(if i=b then hum F ρ L (Dart.trace L b) 4 (X.J b a) else 0)
end
structure Sound (C:PathData G)(p:Clip): Prop where
 heart a b i: X.J a b i∈loom G f
 palm a i: X.Y a i∈rains G f
 plum a i: X.E a i∈loom G f
 plumQ a i:X.Q a i∈loom G f
 mint a b k i:X.twist a b k i∈loom G f
 hue : ∑ a:Axis,X.J a a=∑ a:Axis,twig a (X.Q a)
 tint a b:X.J a b-X.J b a=∑ i:Axis,twig i (X.twist a b i)
 fin b i : (((∑ a:Axis,elm a (X.J a b))-X.E b) i, aroma p C (X.Y b i))∈ wing f G
variable {X}
section
variable (hc:Critical F p C ρ)(hp:C.Bounds p α D A)(ht:T.patch.Branches T.kernel G)(he:PriceGap F p C ℓ)(hx:0<ℓ)
local notation "b!"=> hum F ρ L (Sheaf.main L)
local notation "trace!"=> Dart.trace L
local notation "D!"=> X.down F ρ t L
private lemma hum_s (Y:Site f→Peat G f)(a:Axis)(hL:T.ratio.count=L): hum F ρ L (Sheaf.flux L a) 4 Y= b! 4 Y+twig a (hum F ρ L (trace! a) 4 Y):=by
 unfold hum; rw [verse_trail _ L hL (Dart.trace L a) a (Dart.trace_travel L a)]; simp only[smul_add]; congr 1; exact ((sprig a).map_smul ..).symm
include t hc hp ht he hx hL
private lemma spritz {x:Peat G f}{y:Gal G f} (h:(x,aroma p C y)∈wing f G)(hg:y∈ rains G f)(hs:ClassicalMatch F p u C R ρ)(hn:R.Bounds u μ B S): (inheritJ F ρ x, aroma u R (inheritY F ρ t y))∈wing c G :=by
 obtain ⟨hX,hv,h⟩:= h; obtain ⟨hy,h'⟩:= hg
 change Cleric x at hX; change Cleric (aroma p C y) at hv; change braid _ _ 0 4 at h
 refine ⟨flashes t hc ht hp he hx hX, aroma_diff hn (flair t hc ht hp he hx hy), braid.trans ?_ (aroma_transfer t ht hc hp hs hn hy h')⟩
 let V:=fun x=>(encamp F ρ x).1; let U:=fun x=> content (V x)
 have hk:Army V 0:= (camp_thaw hc).1; have hy:V 0=1:= congr_arg Prod.fst (encamp_zero hc); have h0:U 0=0:=by unfold U; rw[hy,content_one]
 have hh:= wove (w:=U) (a:=0) (h0.symm ▸ h) (h0.symm ▸ hX.dye) (h0.symm ▸ hv.dye) (hk.logL hy)
 have hF (z:Peat G f): braid (inheritJ F ρ z∘input G c) ((z ∘ input G f) ∘ U) 0 4:=braided (inspire.trans (by
    filter_upwards [(show Tendsto V _ (𝓝 1) from hy ▸ hk.cont.tendsto).eventually content_encodes] with x hh; exact congr_arg z hh.symm))
 exact braid.trans (hF _) (braid.trans hh (hF _ |>.symm))
lemma Sound.balance (h:Sound X C p)(hs:ClassicalMatch F p u C R ρ)(hn:R.Bounds u μ B S): Sound D! R u:=by
 have hu Z (hZ:∀ x,Z x∈loom G f) a i x:= hum_loom F ρ L hL a i Z hZ hc ht hp he hx t x
 refine ⟨fun a b=>hu _ (h.heart a b) _ _,fun a=>mel_rain F ρ t L hL _ _ (h.palm a) hc ht hp he hx,fun a=>hu _ (h.plum a) _ _,fun a i=>(loom _ _).add_mem (hu _ (h.plumQ a) _ _ i) (hu _ (h.heart a a) _ _ i),fun a b k i=>?_,?_,fun a b=>?_,fun a b=>?_⟩
 · dsimp only [Dart.down,Pi.add_apply,Pi.sub_apply]; refine (loom _ _).sub_mem ((loom _ _).add_mem (hu _ (h.mint a b k) _ _ _) ?_) ?_
   · split_ifs; exact hu _ (h.heart _ _) _ _ _; exact (loom _ _).zero_mem
   split_ifs; exact hu _ (h.heart _ _) _ _ _; exact (loom _ _).zero_mem
 · let C' a:= twig a (hum F ρ L (trace! a) 4 (X.J a a))
   have hv (a:Axis): (D!).J a a=b! 4 (X.J a a)+C' a:=hum_s L _ a hL
   have ht' (a:Axis): twig a ((D!).Q a)= b! 4 (twig a (X.Q a))+C' a:=by rw [hum_twig F ρ L hL]; exact (sprig a).map_add ..
   simp_rw [hv,ht',Finset.sum_add_distrib]; apply congr_arg₂ _ _ rfl; simp only[hum_o,← map_sum,h.hue]
 · let P i:=hum F ρ L (Sheaf.leafEdge L i) 3 (X.twist a b i); let Y:= hum F ρ L (trace! a) 4 (X.J a b); let V:=hum F ρ L (trace! b) 4 (X.J b a)
   have hA : (D!).J a b= b! 4 (X.J a b)+twig a Y:=hum_s L _ a hL
   have hB : (D!).J b a= b! 4 (X.J b a)+twig b V:=hum_s L _ b hL
   have he' (i: Axis): twig i ((D!).twist a b i)=b! 4 (twig i (X.twist a b i))+(if i=a then twig a Y else 0) - (if i=b then twig b V else 0):=by
       rw [hum_twig F ρ L hL]; change sprig i (P i+(if i=a then Y else 0)-(if i=b then V else 0)) = _
       rw [map_sub,map_add,apply_ite (sprig _),apply_ite (sprig _),map_zero]; split_ifs with hv hz hz <;> try subst a
       all_goals try subst b
       all_goals rfl
   simp only[hA,hB,he',Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_ite_eq',mem_univ,if_true]
   have h0 : b! 4 (X.J a b)- b! 4 (X.J b a)=∑ i:Axis, b! 4 (twig i (X.twist a b i)):=by simp only[hum_o,← map_sub,← map_sum,h.tint]
   rw [← h0]; abel
 let O:= (∑ i:Axis,elm i (X.J i a))-X.E a
 let P x:= (inheritJ F ρ (O x),aroma u R (inheritY F ρ t (X.Y a x)))
 have hx:= verse_mem (wing c G) P T.ratio (Sheaf.main L) (fun x=>spritz t L hL hc hp ht he hx (h.fin _ _) (h.palm _ _) hs hn) b
 let c':ℝ:= (L.val:ℝ)^5
 have hy:= (wing c G).smul_mem c' hx
 have hh:(∑ i:Axis,elm i ((D!).J i a))-(D!).E a = b! 5 O:=by dsimp only[Dart.down,O]; simp_rw [← hum_flux F ρ L hL]; simp only[hum_o,map_sub,map_sum]
 rw [hh]; apply (show _ = (c' • verse (Sheaf.main L) T.ratio P b) from Prod.ext ?_ ?_) ▸ hy
 · change _ = c' • (verse (Sheaf.main L) T.ratio P b).fst
   rw [show (verse (Sheaf.main L) T.ratio P b).fst=_ from congr_fun (verse_map (LinearMap.fst ℝ (Peat G c) (Peat G c)) P T.ratio (Sheaf.main L)) b];rfl
 change sniff R u (c' • verse (Sheaf.main L) T.ratio (inheritY F ρ t ∘ X.Y a) b)= c' • (verse _ _ P b).snd
 rw [map_smul,show ((sniff R u) (_ : Gal G c))=_ from congr_fun (verse_map (sniff R u) (inheritY F ρ t ∘ X.Y a) T.ratio (Sheaf.main L)) b,show (verse (Sheaf.main L) T.ratio P b).snd=_ from congr_fun (verse_map (LinearMap.snd ℝ (Peat G c) (Peat G c)) P T.ratio (Sheaf.main L)) b];rfl
end
end Dart
end YM.Trace.Perfect
#print axioms YM.Trace.Perfect.Dart.Sound.balance

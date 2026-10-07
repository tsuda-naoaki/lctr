<?xml version="1.0"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:m="http://www.w3.org/1998/Math/MathML" exclude-result-prefixes="m">
  <xsl:output method="xml" omit-xml-declaration="yes"/>
  <xsl:strip-space elements="*"/>
  <xsl:template match="m:math"><xsl:apply-templates/></xsl:template>
  <xsl:template match="m:ci"><var name="{normalize-space(.)}"/></xsl:template>
  <xsl:template match="m:apply[m:eq[1]]" priority="2"><app name="relation1.eq"><xsl:apply-templates select="*[position() &gt; 1]"/></app></xsl:template>
  <xsl:template match="m:apply"><app name="{m:csymbol[1]/@cd}.{normalize-space(m:csymbol[1])}"><xsl:apply-templates select="*[position() &gt; 1]"/></app></xsl:template>
  <xsl:template match="m:bind"><bind name="{m:csymbol[1]/@cd}.{normalize-space(m:csymbol[1])}"><vars><xsl:apply-templates select="m:bvar/*"/></vars><xsl:apply-templates select="*[position() &gt; 1 and not(self::m:bvar)]"/></bind></xsl:template>
  <xsl:template match="*"><xsl:message terminate="yes">Unsupported Content MathML element</xsl:message></xsl:template>
</xsl:stylesheet>
